Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.
Require Import Category.Construction.Lift.

Generalizable All Variables.

(* * * Absolute limits and colimits, at cone level / * * 在锥体层面的绝对极限与余极限 *)

(*
 Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §VI.6, book p. 149 (PDF p. 158), item maclane:VI.6:def2
 Book:   Riehl, "Category Theory in Context", 2nd ed., §3.4, Exercise
 3.4.vi(iii), printed p. 109 (PDF p. 129), item
 riehl:3.4:def-absolute (the issue's appended box)
 Paper:  Paré, "On absolute colimits", J. Algebra 19 (1971) 80-95
 nLab:   https://ncatlab.org/nlab/show/absolute+colimit
 nLab:   https://ncatlab.org/nlab/show/preserved+limit

 WHAT THE BOOKS SAY.  Mac Lane, after defining the absolute coequalizer
 (Structure/Coequalizer/Absolute.v): "In the same way one can define
 absolute colimits (or absolute limits) of any other type (Paré
 [1971a])."  Riehl, of the equalizer and the coequalizer of a split
 idempotent (her (i)) and of B as both the limit and the colimit of
 the diagram the idempotent defines (her (ii)): "Prove that the
 aforementioned limits and colimits are preserved by any functor.
 Co/limits with this property are called absolute co/limits."

 THE DEFINITION IS AT CONE LEVEL.  [AbsoluteLimitCone N] says that the
 image [FCone F N] of the cone [N] is a limiting cone for EVERY functor
 [F : C ⟶ D]; [AbsoluteColimitCocone N] is the same for cocones.  The
 image legs are fmap[F] of N's legs, so "preserved" is Mac Lane's §V.4
 sense, [PreservesLimitCone] of Structure/Limit/Preservation.v, and
 not the apex-only [PreservesLimit], whose legs are unconstrained
 (Construction/Comma/Limit.v's note; Structure/Limit/Preservation/
 Separation.v separates the two for one functor).  The predicates
 apply to a bundled [L : Limit K] or [L : Colimit K] through the
 coercion [limit_cone], so absoluteness is predicated of a given
 (co)limit (controls in Test/ProbeAbsolute477.v).

 THE APEX-ONLY PREDICATES THIS DOES NOT REPLACE.  Structure/Limit/
 Constant.v (#356) already declares [AbsoluteLimit G c] and
 [AbsoluteColimit G c]: for every F, the APEX F c carries SOME
 (co)limit structure of F ◯ G.  Those names being taken, the cone-level
 predicates are named like [IsLimitCone] and [PreservesLimitCone].
 The map from the cone-level reading to the apex-only one,
 [AbsoluteLimitCone_apex] and [AbsoluteColimitCocone_apex], lives in
 Constant.v, typed there by [AbsoluteLimit] and [AbsoluteColimit] by
 name; Constant.v requires this file for it, which adds six [Category]
 modules to what a [Require] of Constant.v loads (103 before, 109
 after, by [Print Libraries]).  No converse is proved and no
 separation is attempted, so the apex-only reading is not shown
 strictly weaker.

 THE CLOSURE THEORY.
 - An absolute limit is a limit: [AbsoluteLimitCone_IsLimitCone],
 the instance F := Id, as Mac Lane reads "automatically".  The
 image of N under [Id] has N's apex and legs at [eq_refl]
 ([FCone_Id_apex], [FCone_Id_leg]); only [Id ◯ K] is not [K]
 (refused at [eq_refl] in the probe), so the competing cone is
 repackaged (Preservation.v's [cone_id_comp]).
 - Absoluteness is preservation by every functor:
 [AbsoluteLimitCone_preserves] gives [PreservesLimitCone K F] for
 every F, through Structure/Limit/Comparison.v's
 [PreservesLimitCone_of_cone] (one limiting cone suffices), and
 [AbsoluteLimitCone_of_preserves] is the converse.  The colimit
 side needs that lemma's cocone twin, which the tree did not have;
 #477 adds it beside its twin, as Comparison.v's
 [PreservesColimitCocone_of_cocone], over Preservation.v's
 [FCocone_iso], itself added beside [FCone_iso].
 - It is invariant: along a cone isomorphism
 ([AbsoluteLimitCone_transport]) and hence across limiting cones of
 the same diagram ([AbsoluteLimitCone_limitcone]), so it belongs to
 the limit and not to the cone chosen to represent it.
 - It is closed under functors: the image of an absolute limit under
 any G is absolute ([AbsoluteLimitCone_image], with Preservation.v's
 [cocone_assoc_inv], added beside [cone_assoc_inv], for the colimit
 twin).
 - Each with its colimit twin.

 THE INSTANCES ARE ORDERED.  Each predicate is a family of instances,
 one per target object level (UNIVERSES), and the instances are not
 independent: through Construction/Lift.v's [LiftCat], which re-reads
 a category at higher universe levels, an instance at a target level
 implies the instance at every lower one ([AbsoluteLimitCone_down]),
 and an instance at any level at or above C's own is limiting
 ([AbsoluteLimitCone_IsLimitCone_up]); each with its colimit twin,
 through the duality maps.

 DUALITY IS TWO ONE-LINE MAPS.  [AbsoluteColimitCocone_op] and
 [AbsoluteColimitCocone_of_op] carry an absolute colimit to an absolute
 limit in the opposite and back, through Preservation.v's
 [cone_op_comp] and [cone_op_comp_inv], and are mutually inverse at
 [eq_refl] ([AbsoluteColimitCocone_of_op_op],
 [AbsoluteColimitCocone_op_of_op]).  The two predicates are not one
 term (refused at [eq_refl] in the probe): one quantifies over functors
 out of C, the other out of C^op.  The colimit side's
 [AbsoluteColimitCocone_IsColimitCocone],
 [AbsoluteColimitCocone_transport] and the colimit twins of the lifted
 readings are derived through the maps; the preservation and image
 clauses are built directly, since [FCocone F N] and [FCone F^op N] are
 cones over different functors.

 NON-VACUITY.  Absolute is strictly more than limiting: in the walking
 arrow [_2] the empty cone at [TwoY] is a limit
 ([two_terminal_IsLimitCone]) and is not absolute
 ([two_terminal_not_absolute]): the constant functor at [TwoX] sends
 it to [TwoX], which receives no arrow from [TwoY].  Dually
 [two_initial_IsColimitCocone] and [two_initial_not_absolute].

 STRENGTHS.  The four [Example]s hold at [eq_refl] and are restated in
 the probe.  Every other statement is a map between predicates; none
 is an equation between morphisms.

 UNIVERSES, by [About] on every constant.  [AbsoluteLimitCone@{jo co ch
 do u u0 u1 u2}] is over [J : Category@{jo ch ch}] and
 [C : Category@{co ch ch}] and quantifies over [D : Category@{do ch
 ch}]: every target at any object level [do], a universe OF THE
 PREDICATE, with C's hom-and-proof level.  Its sort [u] lies strictly
 above [do] and [ch] ("do < u", "ch < u"), so the predicate lives
 above the categories it quantifies over, no instance quantifies over
 every category, and the instances form the ordered family above.
 The hom level is shared, and three carriers impose it, each first
 in its own place.  (1) Preservation.v's [cone_leg] and [IsLimitCone]
 are declared over bare binders and minimize to one hom level for a
 shape and its ambient: the probe refuses [IsLimitCone N] over a
 diagram whose shape has strictly smaller hom-sets than its target
 (R7), while accepting the cones themselves (C43).  As [Cone] and
 [Functor] bound a shape's hom level by its ambient's, and [F : C ⟶ D]
 bounds D's below by C's, [IsLimitCone (FCone F N)] alone pins D's hom
 level to C's.  (2) [Compose] (Theory/Functor.v) gives its three
 categories one hom-and-proof level, and [FCone] is over [F ◯ K]: the
 probe refuses [F ◯ K] with C's homs strictly below D's while
 accepting [C ⟶ D] itself (R3, C10).  (3) For cocones,
 [Opposite_Functor] (Functor/Opposite.v) gives its source and target
 one hom level, and [Cocone F] is [Cone (F^op)] (Structure/Cone.v):
 the probe refuses [F^op] for a functor whose source has strictly
 smaller hom-sets than its target (R8).  None of the three is
 structural.  The same definitions with their binders written out
 compile with the shape's or source's hom level at or below the
 other's: [cone_leg] and [IsLimitCone] (C41, accepted where R7 is
 refused, C44), and [Opposite_Functor] (C42, with cones over it, C45);
 [Compose], over three hom levels with the same two obligation proofs,
 was measured in a scratch file and is not pinned here.  Lifting the
 cap is therefore a matter of annotating those binders tree-wide,
 which #477 does not attempt.  The cap does exclude part of Riehl's
 "any functor": the probe accepts the Yoneda embedding of C as a
 target when C's objects lie strictly below its hom-sets (C46) and
 refuses it when they lie strictly above (R11).
 The binders are written out on every constant of the predicates and
 their closure theory, and no block carries an equation; the
 non-vacuity constants leave theirs to Rocq, and [empty_shape_cocone]
 comes out over categories whose hom level is [Set] only, carrier (3)
 identifying the hom levels of [_0] and its target and [_0]'s being
 [Set].  [AbsoluteLimitCone_IsLimitCone] consumes the instance whose
 target is C's own levels, [AbsoluteLimitCone@{jo co ch co …}], which
 is what "take F := Id" means; the probe refuses it from a target
 object level above C's (R4), a pin of that lemma's signature and not
 of what the predicate yields: R4's statement is accepted through
 [AbsoluteLimitCone_IsLimitCone_up] (C22) and through
 [AbsoluteLimitCone_down] (C23), and their colimit twins likewise
 (C24, C25).  [AbsoluteLimitCone_IsLimitCone_up@{jo co ch do …}]
 carries "co <= do", and [AbsoluteLimitCone_down@{jo co ch do eo …}]
 "do <= eo", with no equation; their statements, and their colimit
 twins', name the instances of the predicate they consume and produce
 (six explicit universe instances in four constants), since a level
 bounded below by C's alone would otherwise be minimized to C's.  The
 preservation, transport and image clauses keep [do] free, the
 preservation clauses by taking the limit property as a separate
 hypothesis (consuming the [Id] instance there identified [do] with
 [co], measured).  The non-vacuity results sit at hom level [Set], the
 level of [_0] and [_2].

 STALE PREMISES, dated from gh.  The issue (filed 2026-07-23, the Riehl
 box appended 2026-07-31) says no [Absolute*] identifier exists; that
 was accurate when written and is stale since PR #1229 (merged
 2026-08-31, for #356), which added Constant.v's apex-only predicates.

 NOT DELIVERED.  Paré's theorems: the characterization of absolute
 colimits (preservation by the Yoneda embedding) and of absolute
 coequalizers by splittings.  Any separation of the cone-level and
 apex-only readings.  Absoluteness relative to a class of target
 categories, or to a universe-free reading.  The cone-level
 predicates at a target hom level other than C's, which waits on the
 annotation of the three carriers above.  Riehl's split idempotents
 (issue #957) and Beck's absolute condition (issue #484), which
 consume these predicates. 

 --------
 书籍：   Mac Lane，《工作数学家的范畴》，第2版，§VI.6，第149页（PDF第158页），条目 maclane:VI.6:def2
 书籍：   Riehl，《上下文中的范畴论》，第2版，§3.4，练习 3.4.vi(iii)，印刷版第109页（PDF第129页），条目 riehl:3.4:def-absolute（问题附加框）
 论文：   Paré，《关于绝对余极限》，《代数杂志》 19 (1971) 80-95
 nLab：    https://ncatlab.org/nlab/show/absolute+colimit 
 nLab：    https://ncatlab.org/nlab/show/preserved+limit书中所说。Mac Lane 在定义绝对共等化子 (Structure/Coequalizer/Absolute.v) 后写道：“以同样的方式，可以定义任何其他类型的绝对余极限（或绝对极限）（Paré [1971a]）。” Riehl 关于分裂幂等子的等化子和共等化子（她的 (i)）以及将 B 作为幂等子定义的图的极限和余极限（她的 (ii)）写道：“证明上述极限和余极限会被任何函子保持。具有这种性质的极限/余极限称为绝对极限/余极限。”该定义适用于圆锥层级。[AbsoluteLimitCone N] 表示圆锥 [N] 的像 [FCone F N] 是每个函子 [F : C ⟶ D] 的极限圆锥；[AbsoluteColimitCocone N] 对余圆锥也是相同的。像的腿是 N 的腿的 fmap [F]，因此“保持”是 Mac Lane 第 V.4 节的含义，[PreservesLimitCone] 来自 Structure/Limit/Preservation.v，而不是仅仅是顶点的 [PreservesLimit]，其腿不受约束（Construction/Comma/Limit.v 的注释；Structure/Limit/Preservation/Separation.v 对单个函子区分了两者）。这些谓词可通过强制 [limit_cone] 适用于绑定的 [L : Limit K] 或 [L : Colimit K]，因此绝对性是以给定的（余）极限为前提的（在 Test/ProbeAbsolute477.v 中控制）。仅顶点的谓词，这并未替代这些。Structure/Limit/Constant.v（#356）已经声明了[AbsoluteLimit G c]和[AbsoluteColimit G c]：对于每个F，顶点F c承载某种F ◯ G的（共）极限结构。由于这些名称已被使用，锥层级的谓词被命名为[IsLimitCone]和[PreservesLimitCone]。从锥层级读取到仅顶点读取的映射，[AbsoluteLimitCone_apex]和[AbsoluteColimitCocone_apex]，位于Constant.v中，由[AbsoluteLimit]和[AbsoluteColimit]以名称形式在其中类型化；Constant.v需要此文件，其在加载[Require]的Constant.v时增加了六个[Category]模块（之前103，之后109，按[Print Libraries]计算）。未证明反向，也未尝试分离，因此未显示仅顶点读取严格较弱。闭合理论。——绝对极限就是极限：[AbsoluteLimitCone_IsLimitCone]，实例 F := Id，如 Mac Lane 所说“自动”。N 在 [Id] 下的像在 [eq_refl] 处有 N 的顶点和边 ([FCone_Id_apex], [FCone_Id_leg])；只有 [Id ◯ K] 不是 [K]（在探针 [eq_refl] 处被拒绝），所以竞争锥被重新打包（Preservation.v 的 [cone_id_comp]）。——绝对性是指被每一个函子保持：[AbsoluteLimitCone_preserves] 对每个 F 都给出 [PreservesLimitCone K F]，通过 Structure/Limit/Comparison.v 的 [PreservesLimitCone_of_cone]（一个限制锥即可），而 [AbsoluteLimitCone_of_preserves] 是其逆。余极限一边需要该引理的余锥孪生，但树中没有；#477 将它添加在它的孪生旁边，作为 Comparison.v 的 [PreservesColimitCocone_of_cocone]，位于 Preservation.v 的 [FCocone_iso] 之上，自身添加在 [FCone_iso] 旁。- 它是不变的：沿着一个圆锥同构 ([AbsoluteLimitCone_transport]) 并因此在同一图的极限圆锥上 ([AbsoluteLimitCone_limitcone])，所以它属于极限而不属于用于表示它的圆锥。- 它在函子下闭合：在任何 G 下绝对极限的像都是绝对的 ([AbsoluteLimitCone_image]，带有 Preservation.v 的 [cocone_assoc_inv]，添加在 [cone_assoc_inv] 旁边，用于余极限对应项)。- 每个都有其余极限对应项。实例是有序的。每个谓词是一族实例，每个目标对象层次（宇宙）有一个实例，且这些实例不是独立的：通过 Construction/Lift.v 中的 [LiftCat]，它会在更高的宇宙层次重新读取一个范畴，某个目标层次的实例意味着每个更低层次的实例（[AbsoluteLimitCone_down]），且任何在 C 自身层次或以上的实例都是限制性的（[AbsoluteLimitCone_IsLimitCone_up]）；每个实例都有其余极的对应实例，通过对偶映射实现。二重性是两个单线映射。[AbsoluteColimitCocone_op] 和 [AbsoluteColimitCocone_of_op] 将绝对余极限传递到相反方向的绝对极限，再返回，通过 Preservation.v 的 [cone_op_comp] 和 [cone_op_comp_inv]，并在 [eq_refl]（[AbsoluteColimitCocone_of_op_op]、[AbsoluteColimitCocone_op_of_op]）处互为逆。两个谓词不是同一个项（在探针的 [eq_refl] 处被拒绝）：一个对 C 出来的函子进行量化，另一个对 C^op 出来的函子进行量化。余极限侧的 [AbsoluteColimitCocone_IsColimitCocone]、[AbsoluteColimitCocone_transport] 以及提升读数的余极限双胞通过映射导出；保留和像子条款则直接构建，因为 [FCocone F N] 和 [FCone F^op N] 是不同函子上的锥体。非空性。绝对性严格上比极限更强：在行进箭头 [_2] 中，[TwoY] 处的空圆锥是一个极限（[two_terminal_IsLimitCone]），但不是绝对的（[two_terminal_not_absolute]）；[TwoX] 处的常函子将其映射到 [TwoX]，它没有接收来自 [TwoY] 的箭头。对偶地，[two_initial_IsColimitCocone] 和 [two_initial_not_absolute]。

 强度。四个 [Example] 在 [eq_refl] 处成立，并在探针中重述。每一个其他陈述都是谓词之间的映射；没有一个是态射之间的方程。多元宇宙，由 [About] 在每个常量上。[AbsoluteLimitCone@{jo co ch do u u0 u1 u2}] 位于 [J : Category@{jo ch ch}] 和 [C : Category@{co ch ch}] 之上，并且对 [D : Category@{do ch ch}] 进行量化：在任何对象层次上的每个目标 [do]，一个谓词的宇宙，具有 C 的同态与证明层次。它的类型 [u] 严格位于 [do] 和 [ch] 之上（"do < u"，"ch < u"），因此谓词位于它量化的类别之上，没有实例对每个类别进行量化，并且这些实例形成上述的有序族群。其同态层次是共享的，并且三个承载者施加了它，每个承载者在各自的位置上首先出现。(1) Preservation.v 的 [cone_leg] 和 [IsLimitCone] 是在裸绑定器上声明的，并将形状及其环境的同态级别最小化到一个同态级别：探针拒绝在其形状的同态集严格小于目标的图表上使用 [IsLimitCone N] (R7)，同时接受锥体本身 (C43)。由于 [Cone] 和 [Functor] 将一个形状的同态级别绑定到其环境的同态级别，并且 [F : C ⟶ D] 将 D 的同态级别约束在 C 之下，只有 [IsLimitCone (FCone F N)] 将 D 的同态级别固定到 C 上。(2) [Compose] (Theory/Functor.v) 给它的三个范畴赋予一个同态和证明级别，而 [FCone] 是在 [F ◯ K] 上：探针拒绝在 C 的同态严格低于 D 的情况下使用 [F ◯ K]，同时接受 [C ⟶ D] 本身 (R3, C10) 。(3) 对于余锥，
 [Opposite_Functor]（Functor/Opposite.v）给出了它的源和目标的一个同态层级，而 [Cocone F] 是 [Cone (F^op)]（Structure/Cone.v）：
 对于源的同态集严格小于目标的函子，探针拒绝 [F^op]（R8）。这三者都不是结构性的。将相同的定义与它们的绑定器展开后编译时，其形状的或源的同态层级在另一个之下或相等：[cone_leg] 和 [IsLimitCone]（C41，在 R7 被拒绝时接受，C44），以及 [Opposite_Functor]（C42，在其上有锥，C45）；[Compose]，在三个同态层级上使用相同的两个义务证明，在一个草稿文件中测量过，未在这里固定。因此，提高上限是一个对这些绑定器进行全树注解的问题，而 #477 并未尝试。这个上限确实排除了Riehl的“任何函子”的一部分：当C的对象严格低于其同态集（C46）时，探针接受C的Yoneda嵌入作为目标；当它们严格高于时（R11），则拒绝。绑定器在谓词的每个常量及其闭包理论上都被写出，并且没有块携带方程；非空常量将其留给Rocq，而[empty_shape_cocone]仅出现在同态水平为[Set]的范畴上，载体（3）标识[_0]及其目标的同态水平，以及[_0]的同态水平为[Set]。[AbsoluteLimitCone_IsLimitCone] 消耗目标为 C 自身层级的实例 [AbsoluteLimitCone@{jo co ch co …}]，这就是“take F := Id”的意思；探针会拒绝来自高于 C 层级的目标对象（R4）的实例，这是该引理签名中的一个固定值，而不是谓词产生的内容：R4 的声明通过 [AbsoluteLimitCone_IsLimitCone_up]（C22）和 [AbsoluteLimitCone_down]（C23）被接受，它们的余极限双子也同样被接受（C24, C25）。[AbsoluteLimitCone_IsLimitCone_up@{jo co ch do …}] 承载“co <= do”，[AbsoluteLimitCone_down@{jo co ch do eo …}] 承载“do <= eo”，没有等式；它们的声明及其余极限双子命名了它们所消耗和产生的谓词实例（在四个常量中有六个显式的宇宙实例），因为仅由 C 限定的下界层级否则将被最小化为 C 的层级。保存、传输和图像条款保持 [do] 空闲，保存条款通过将极限属性作为单独的假设（在此消耗 [Id] 实例，该实例被识别为 [do] 与 [co]，已测量）来实现。非空结果处于同伦层级 [Set]，即 [_0] 和 [_2] 的层级。

 陈旧前提，来自 gh。该问题（提交于 2026-07-23，Riehl 盒附加于 2026-07-31）表明不存在 [Absolute*] 标识符；在编写时这是准确的，并且自 PR #1229（合并于 2026-08-31，为 #356）添加 Constant.v 的仅顶点谓词以来已过时。未送达。Paré 的定理：绝对余极限的表征（由 Yoneda 嵌入保持）以及通过分裂的绝对等化器的表征。锥层和仅顶点读法的任何分离。相对于一类目标范畴的绝对性，或相对于无宇宙读法的绝对性。在目标 Hom 层级（非 C 的）上的锥层谓词，依赖于上述三个载体的标注。Riehl 的分裂幂等元（问题 #957）和 Beck 的绝对条件（问题 #484），使用这些谓词。
*)

(** ** The two predicates / ** 两个谓词 *)

Definition AbsoluteLimitCone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) : Type :=
  ∀ (D : Category@{do ch ch}) (F : C ⟶ D), IsLimitCone (FCone F N).

Definition AbsoluteColimitCocone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cocone K) : Type :=
  ∀ (D : Category@{do ch ch}) (F : C ⟶ D), IsColimitCocone (FCocone F N).

(** ** An absolute limit is a limit / ** 绝对极限是极限 *)

(* The image of N under [Id] is N on the nose, apex and legs. / 在 [Id] 下，N 的像是在鼻子、顶点和腿上的 N。 *)

Example FCone_Id_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) : vertex_obj[FCone Id N] = vertex_obj[N] := eq_refl.

Example FCone_Id_leg@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) (x : J) : cone_leg (FCone Id N) x = cone_leg N x := eq_refl.

(* "Take F := Id": the instance whose target is C's own levels, with the competing cone repackaged by Preservation.v's [cone_id_comp]. / “取 F := Id”：该实例的目标是 C 自身的层次，竞争圆锥通过 Preservation.v 的 [cone_id_comp] 重新打包。 *)

Definition AbsoluteLimitCone_IsLimitCone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone N) : IsLimitCone N :=
  fun M => A C Id (cone_id_comp M).

(* * ** Duality: an absolute colimit is an absolute limit in the opposite / * ** 二元性：绝对余极限在对偶下是绝对极限 *)

Definition AbsoluteColimitCocone_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  @AbsoluteLimitCone (J^op) (C^op) (K^op) N :=
  fun D F M =>
    A (D^op)%category (F^op)%functor
      (@cone_op_comp_inv J C (D^op)%category K (F^op)%functor M).

Definition AbsoluteColimitCocone_of_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone N :=
  fun D F M => A (D^op)%category (F^op)%functor (cone_op_comp M).

Example AbsoluteColimitCocone_of_op_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone_of_op (AbsoluteColimitCocone_op A) = A := eq_refl.

Example AbsoluteColimitCocone_op_of_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone_op (AbsoluteColimitCocone_of_op A) = A := eq_refl.

Definition AbsoluteColimitCocone_IsColimitCocone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) : IsColimitCocone N :=
  AbsoluteLimitCone_IsLimitCone (AbsoluteColimitCocone_op A).

(* * ** Every instance at or above C's levels: the lift / * ** 每个在 C 级或以上的实例：电梯 *)

(*
 An absolute limit at ANY target object level at or above C's is a
 limit: C is read at that level by Construction/Lift.v's [LiftCat], and
 [Lift_in C] plays the part of [Id].  The instance of the hypothesis is
 named, the target level [do] being bounded below by [co] alone. 

 --------
 在任何目标对象级别为 C 或以上的绝对极限是一个极限：C 在该级别由 Construction/Lift.v 的 [LiftCat] 读取，而 [Lift_in C] 扮演 [Id] 的角色。假设的实例被命名，目标级别 [do] 仅被 [co] 限定下限。
*)

Definition AbsoluteLimitCone_IsLimitCone_up@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N) :
  IsLimitCone N.
Proof.
  intro M.
  pose (Ml := @Build_Cone J (LiftCat C) (Lift_in C ◯ K)
                (@vertex_obj _ _ _ M)
                (@Build_ACone J (LiftCat C) (@vertex_obj _ _ _ M)
                   (Lift_in C ◯ K)
                   (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
                   (fun x y f =>
                      @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f))).
  pose (U := A (LiftCat C) (Lift_in C) Ml).
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - intro x. exact (unique_property U x).
  - intros v Hv. exact (uniqueness U v Hv).
Defined.

Definition AbsoluteColimitCocone_IsColimitCocone_up@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone@{jo co ch do _ _ _ _} N) :
  IsColimitCocone N :=
  AbsoluteLimitCone_IsLimitCone_up (AbsoluteColimitCocone_op A).

(*
 Each instance implies every lower one: a target D at a level below the
 hypothesis' is read at that level, and [Lift_after F] replaces F. 

 --------
 每个实例都暗示了其下层的每一个：位于假设之下的目标 D 会在该层读取，而 [Lift_after F] 替代 F。
*)

Definition AbsoluteLimitCone_down@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone@{jo co ch eo _ _ _ _} N) :
  AbsoluteLimitCone@{jo co ch do _ _ _ _} N.
Proof.
  intros D F M.
  pose (Ml := @Build_Cone J (LiftCat D) (Lift_after F ◯ K)
                (@vertex_obj _ _ _ M)
                (@Build_ACone J (LiftCat D) (@vertex_obj _ _ _ M)
                   (Lift_after F ◯ K)
                   (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
                   (fun x y f =>
                      @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f))).
  pose (U := A (LiftCat D) (Lift_after F) Ml).
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - intro x. exact (unique_property U x).
  - intros v Hv. exact (uniqueness U v Hv).
Defined.

Definition AbsoluteColimitCocone_down@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone@{jo co ch eo _ _ _ _} N) :
  AbsoluteColimitCocone@{jo co ch do _ _ _ _} N :=
  AbsoluteColimitCocone_of_op
    (AbsoluteLimitCone_down (AbsoluteColimitCocone_op A)).

(* * ** Absoluteness is preservation by every functor / * ** 绝对性是被每个函子保持 *)

Definition AbsoluteLimitCone_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (HN : IsLimitCone N) (A : AbsoluteLimitCone N)
  (D : Category@{do ch ch}) (F : C ⟶ D) : PreservesLimitCone K F :=
  PreservesLimitCone_of_cone F N HN (A D F).

Definition AbsoluteLimitCone_of_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (HN : IsLimitCone N)
  (P : ∀ (D : Category@{do ch ch}) (F : C ⟶ D), PreservesLimitCone K F) :
  AbsoluteLimitCone N :=
  fun D F => P D F N HN.

Definition AbsoluteColimitCocone_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (HN : IsColimitCocone N) (A : AbsoluteColimitCocone N)
  (D : Category@{do ch ch}) (F : C ⟶ D) : PreservesColimitCocone K F :=
  PreservesColimitCocone_of_cocone F N HN (A D F).

Definition AbsoluteColimitCocone_of_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (HN : IsColimitCocone N)
  (P : ∀ (D : Category@{do ch ch}) (F : C ⟶ D),
         PreservesColimitCocone K F) :
  AbsoluteColimitCocone N :=
  fun D F => P D F N HN.

(* * ** Invariance: along cone isomorphisms, and across limiting cones / * ** 不变性：沿圆锥同构，以及跨限制圆锥 *)

Definition AbsoluteLimitCone_transport@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cone K} (i : ConeIso N M) (A : AbsoluteLimitCone N) :
  AbsoluteLimitCone M :=
  fun D F => limitcone_transport (FCone_iso F i) (A D F).

Definition AbsoluteColimitCocone_transport@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cocone K} (i : ConeIso N M) (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone M :=
  AbsoluteColimitCocone_of_op
    (AbsoluteLimitCone_transport i (AbsoluteColimitCocone_op A)).

(* Absoluteness belongs to the diagram's limit, not to the cone chosen to represent it: any other limiting cone is absolute too. / 绝对性属于图表的极限，而不是所选择的锥体来表示它：任何其他极限锥体也是绝对的。 *)

Definition AbsoluteLimitCone_limitcone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cone K} (HN : IsLimitCone N) (HM : IsLimitCone M)
  (A : AbsoluteLimitCone N) : AbsoluteLimitCone M :=
  AbsoluteLimitCone_transport (limitcone_iso HN HM) A.

Definition AbsoluteColimitCocone_colimitcocone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cocone K} (HN : IsColimitCocone N) (HM : IsColimitCocone M)
  (A : AbsoluteColimitCocone N) : AbsoluteColimitCocone M :=
  AbsoluteColimitCocone_transport (colimitcocone_iso HN HM) A.

(* * ** Closure under functors: the image of an absolute limit is absolute / * ** 在函子下的封闭性：绝对极限的像是绝对的 *)

Definition AbsoluteLimitCone_image@{jo co ch eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {E : Category@{eo ch ch}} {K : J ⟶ C} {N : Cone K}
  (A : AbsoluteLimitCone N) (G : C ⟶ E) : AbsoluteLimitCone (FCone G N) :=
  fun D H => islimitcone_assoc (A D (H ◯ G)).

Definition AbsoluteColimitCocone_image@{jo co ch eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {E : Category@{eo ch ch}} {K : J ⟶ C} {N : Cocone K}
  (A : AbsoluteColimitCocone N) (G : C ⟶ E) :
  AbsoluteColimitCocone (FCocone G N) :=
  fun D H M => A D (H ◯ G) (cocone_assoc_inv M).

(* * ** Non-vacuity: a limit and a colimit that are not absolute / * ** 非空性：一个既不是极限也不是余极限的情况 *)


(* Cones and cocones over a diagram of the empty shape are bare apexes. / 空形状图上的锥和余锥是裸顶点。 *)

Definition empty_shape_cone {C : Category} (G : _0 ⟶ C) (c : C) : Cone G.
Proof.
  unshelve refine (@Build_Cone _0 C G c _).
  unshelve econstructor; intro x; destruct x.
Defined.

Definition empty_shape_cocone {C : Category} (G : _0 ⟶ C) (c : C) :
  Cocone G.
Proof.
  unshelve refine (@Build_Cone (_0^op) (C^op) (G^op) c _).
  unshelve econstructor; intro x; destruct x.
Defined.

(* In the walking arrow [_2], [TwoY] is terminal and [TwoX] initial. / 在行走箭头 [_2] 中，[TwoY] 是终端，[TwoX] 是初始。 *)

Definition two_into_TwoY (m : TwoObj) : TwoHom m TwoY :=
  match m with TwoX => TwoXY | TwoY => TwoIdY end.

Definition two_out_of_TwoX (m : TwoObj) : TwoHom TwoX m :=
  match m with TwoX => TwoIdX | TwoY => TwoXY end.

Definition two_terminal_IsLimitCone :
  IsLimitCone (empty_shape_cone (From_0 _2) (TwoY : _2)).
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (two_into_TwoY (@vertex_obj _ _ _ M)).
  - intro x; destruct x.
  - intros v _; apply Two_thin.
Defined.

Definition two_initial_IsColimitCocone :
  IsColimitCocone (empty_shape_cocone (From_0 _2) (TwoX : _2)).
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (two_out_of_TwoX (@vertex_obj _ _ _ M)).
  - intro x; destruct x.
  - intros v _; apply Two_thin.
Defined.

(*
 The constant functor at [TwoX] sends the terminal [TwoY] to [TwoX],
 which receives no arrow from [TwoY]; dually the constant functor at
 [TwoY] sends the initial [TwoX] to [TwoY]. 

 --------
 在  [TwoX] 上的恒等函子将终端对象  [TwoY]  映射到  [TwoX] ，而  [TwoY]  不会有箭头指向它；对偶地，在  [TwoY] 上的恒等函子将初始对象  [TwoX]  映射到  [TwoY] 。
*)

Theorem two_terminal_not_absolute :
  AbsoluteLimitCone (empty_shape_cone (From_0 _2) (TwoY : _2)) → False.
Proof.
  intro A.
  destruct (A _2 Δ[_2]((TwoX : _2))
              (empty_shape_cone (Δ[_2]((TwoX : _2)) ◯ From_0 _2)
                 (TwoY : _2)))
    as [u _ _].
  exact (TwoHom_Y_X_absurd u).
Qed.

Theorem two_initial_not_absolute :
  AbsoluteColimitCocone (empty_shape_cocone (From_0 _2) (TwoX : _2)) →
  False.
Proof.
  intro A.
  destruct (A _2 Δ[_2]((TwoY : _2))
              (empty_shape_cocone (Δ[_2]((TwoY : _2)) ◯ From_0 _2)
                 (TwoX : _2)))
    as [u _ _].
  exact (TwoHom_Y_X_absurd u).
Qed.
