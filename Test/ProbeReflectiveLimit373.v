Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Construction.Reflective.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.TorsionFree.

Generalizable All Variables.

(** * Boundary probe for Construction/Reflective/Limit.v (issue #373) / * 用于 Construction/Reflective/Limit.v 的边界探针（问题 #373） *)

(*
Every boundary the target file's header states as measured is pinned
   here, from OUTSIDE that file: an in-file negative renames in lockstep
   with the constant it guards and so cannot detect a rename.  The
   [Require] list above mirrors the target's exactly, plus this file's own
   target and the four modules the concrete witness needs.

   Eight negatives of THREE kinds, kept lexically apart, plus one
   scope-free instrument check:

     CONVERSION  1  the two routes to [PreservesLimitCone K (Incl C S)]
                    are not the same term
     CONVERSION  2  ... nor do their produced mediators agree on the nose
     CONVERSION  3  [reflective_counit_iso]'s forward leg is not the
                    counit on the nose (that lemma is closed with [Qed]
                    while producing data)
     TYPING      4  [CreatesLimit] is not [PreservesLimitCone]
     TYPING      5  [CreatesLimit] is not [StrictlyCreatesLimit]
     FORMABILITY 6  [Subcategory] identifies its category's hom and proof
                    universes
     FORMABILITY 7  [cone_leg] identifies the shape's hom-and-proof level
                    with the ambient category's
     FORMABILITY 8  ... and so does [IsLimitCone], separately

   Negatives 7 and 8 sit on a DIFFERENT axis from negative 6 (two
   categories' levels, rather than one category's hom against its proof),
   and each is testable apart from the others: [Cone F] and [Ju ⟶ Cu] are
   both accepted at the very levels where they are rejected, so neither
   [Cone] nor [Functor] is a donor.

   Each negative was stripped ONE AT A TIME, with the others left as
   [Fail], and the whole error read.  Negatives 4 and 5 report a plain
   "has type ... while it is expected to have type ...", with no "cannot
   unify" clause and no universe clause; negatives 1-3 end in "cannot
   unify"; negative 6 ends in "universe inconsistency: Cannot enforce
   cp = ch because ch < cp", and negatives 7 and 8 in "universe
   inconsistency: Cannot enforce vh = jh because jh < vh".

   Every constant a negative names also appears outside a [Fail], in a
   control below.  The controls were checked by rename simulation: each
   such constant was renamed throughout this file, and the file then
   stopped compiling at a control rather than compiling with a vacuously
   green [Fail].

--------
目标文件头中声明测量的每个边界都在此固定，来自该文件之外：文件内的负重命名与它所保护的常量同步，因此无法检测重命名。上面的 [Require] 列表完全镜像了目标的内容，此外还有该文件自身的目标以及具体证人所需的四个模块。

三种八个否定，按词汇分开，再加一个无作用域的工具检查：

转换 1 到 [PreservesLimitCone K (Incl C S)] 的两条路径不是同一项
转换 2 …它们产生的介质也不完全一致
转换 3 [reflective_counit_iso] 的前向部分不是完全的余单位（该引理在生成数据时由 [Qed] 完成）
类型 4 [CreatesLimit] 不是 [PreservesLimitCone]
类型 5 [CreatesLimit] 不是 [StrictlyCreatesLimit]
可形成性 6 [Subcategory] 确认其类别的同态和证明宇宙
可形成性 7 [cone_leg] 将形状的同态-证明层与环境类别的层对应起来
可形成性 8 … [IsLimitCone] 也是如此，独立进行

负面 7 和 8 位于与负面 6 不同的轴上（两个类别的水平，而不是一个类别对其证据的对比），且每一个都可以独立于其他进行测试：[Cone F] 和 [Ju ⟶ Cu] 在它们被拒绝的同一级别上都被接受，所以 [Cone] 和 [Functor] 不是供体。

每个负例都是一次一个地剥除的，其余的保持为 [Fail]，并读取整个错误。负例 4 和 5 报告了一个简单的“类型为 ...，但预期类型为 ...”，没有“无法统一”条款，也没有宇宙条款；负例 1-3 以“无法统一”结尾；负例 6 以“宇宙不一致：无法强制执行 cp = ch 因为 ch < cp”结尾，负例 7 和 8 则以“宇宙不一致：无法强制执行 vh = jh 因为 jh < vh”结尾。

每个常量a negative names也出现在[Fail]之外，在下面的控制中。通过重命名模拟检查了这些控件：每个这样的常量在整个文件中都被重命名，然后文件在一个控制处停止编译，而不是以空泛绿色的[Fail]编译。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
If this command ever succeeds, the [Fail] wrapper is not doing its job
   and every negative below is worthless.

--------
如果这个命令成功了，[Fail] 包装器就没有起作用，下面的每一个负面都是毫无意义的。
*)

Fail Check probe373_no_such_constant_anywhere.

Section Boundaries.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** Controls / ** 控制 *)

Check (Subcategory C).
Check (Sub C S).
Check (Incl C S).
Check (reflector R).
Check (reflective_adj R).
Check (reflective_CreatesLimit R K : CreatesLimit K (Incl C S)).
Check (reflective_Incl_PreservesLimitCone R K
         : PreservesLimitCone K (Incl C S)).
Check (fun L : Limit (Incl C S ◯ K) =>
         creation_preserves_limit (reflective_CreatesLimit R K) L).
Check (fun x : Sub C S => to (reflective_counit_iso R x)).
Check (fun x : Sub C S =>
         @counit _ _ (reflector R) (Incl C S) (reflective_adj R) x).
Check (fun (N : Cone K) (H : IsLimitCone N) => unique_obj (H N)).
Check (fun (N : Cone K) (x : J) => cone_leg N x).
Check (fun (N : Cone K) => FCone (Incl C S) N).
Check (@StrictlyCreatesLimit J (Sub C S) C K (Incl C S)).
Check (fun (L : Limit (Incl C S ◯ K)) (M : Cone K) (HM : IsLimitCone M)
           (P : Cone (Incl C S ◯ K)) =>
         reflective_two_routes_agree R K L M HM P).
Check (reflective_inherits_limits R K).
Check (reflective_lift R K).
Check (reflective_CreatesAllLimits R).
Check (reflective_Complete R).

(** ** CONVERSION 1: the two preservation routes are different terms / ** 转换 1：这两种保存方式是不同的术语 *)

Fail Example probe_two_routes (L : Limit (Incl C S ◯ K)) :
  creation_preserves_limit (reflective_CreatesLimit R K) L
    = reflective_Incl_PreservesLimitCone R K := eq_refl.

(** ** CONVERSION 2: ... and their mediators do not agree on the nose / ** 转换 2：……他们及其调解人对于鼻子没有达成一致 *)

Fail Example probe_two_routes_med (L : Limit (Incl C S ◯ K))
  (M : Cone K) (HM : IsLimitCone M) (P : Cone (Incl C S ◯ K)) :
  unique_obj
    (creation_preserves_limit (reflective_CreatesLimit R K) L M HM P)
    = unique_obj (reflective_Incl_PreservesLimitCone R K M HM P) := eq_refl.

(** ** CONVERSION 3: the counit isomorphism does not reduce / ** 转换 3：余单位同构不简化 *)

(*
[reflective_counit_iso] (Construction/Reflective.v) produces data
   and is closed with [Qed], so its forward leg does not reduce to the
   counit.  This is a second, independent reason -- beyond the structural
   one recorded in the target's header, that the lemma speaks about an
   object of the subcategory rather than an arbitrary object of C -- why
   it does not shorten the comparison isomorphism.

--------
[reflective_counit_iso]（Construction/Reflective.v）产生数据，并且由 [Qed] 关闭，因此它的前向部分不会简化为余单位。这是第二个、独立的原因——除目标头中记录的结构性原因之外，该引理谈论的是子范畴的对象而不是 C 的任意对象——解释了为什么它不会缩短比较同构。
*)

Fail Example probe_counit_iso_leg (x : Sub C S) :
  to (reflective_counit_iso R x)
    = @counit _ _ (reflector R) (Incl C S) (reflective_adj R) x := eq_refl.

(** ** TYPING 4: creation is not preservation / ** 类型4：创造不是保存 *)

Fail Check (reflective_CreatesLimit R K
              : PreservesLimitCone K (Incl C S)).

(** ** TYPING 5: creation is not STRICT creation / ** 打字 5：创造不是严格的创造 *)

(*
[StrictLift]'s [slift_eq] field (Structure/Limit/Creation.v) asks
   for a LEIBNIZ equality of apexes downstairs.  The lift built in the
   target has apex [Incl C S (reflector R L)], which the comparison
   isomorphism relates to L but does not equate to it.

--------
[StrictLift] 的 [slift_eq] 字段（Structure/Limit/Creation.v）要求楼下顶点的 LEIBNIZ 相等性。目标中建造的电梯具有顶点 [Incl C S (reflector R L)]，该比较同构将其与 L 关联，但并不等同于 L。
*)

Fail Check (reflective_CreatesLimit R K
              : StrictlyCreatesLimit K (Incl C S)).

End Boundaries.

(** ** FORMABILITY 6: [Subcategory] identifies hom with proof / ** 可塑性 6：[Subcategory] 识别 hom 并提供证明 *)

(*
The target's constants are all over [Category@{u u0 u0}], and the
   identification is inherited rather than introduced: [Subcategory]
   alone already forces it, with the category's own hom-set and identity
   accepted at the very levels where [Subcategory] is rejected.  The
   identification sits in [Subcategory]'s BINDER; its constraint block is
   empty.

--------
目标的常量全部集中在 [Category@{u u0 u0}] 上，并且标识是继承而来的，而不是引入的：仅 [Subcategory] 就已经强制了它，类别自身的同态集和标识在 [Subcategory] 被拒绝的层次上被接受。标识位于 [Subcategory] 的 BINDER 中；它的约束块是空的。
*)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@homset Cu xu yu).

Fail Check (Subcategory Cu).

End UniverseProbe.

(** ** FORMABILITY 7 and 8: the cone vocabulary identifies J with C / ** 可成型性 7 和 8：圆锥词汇将 J 与 C 关联 *)

(*
The shape-indexed constants of the target additionally carry [u0 = u8],
   collapsing the shape's hom-and-proof level onto the ambient category's.
   That is the cone vocabulary's doing, not the functor's and not the
   [Cone] record's: with the shape's hom level declared strictly BELOW the
   ambient one, the functor type and the [Cone] record are both formable,
   while [cone_leg] and [IsLimitCone] are each rejected on their own.
   These are the same donor family Structure/Limit/Initial.v's header
 records for a RELATED collapse; the axis there is the
   shape's own hom against its own proof, and it names [IsALimit] as a
   third donor.  [IsALimit] is a donor on THIS axis too, as are [Limit],
   [ConeIso] and [FCone], each rejected alone at these levels while
   [vertex_obj] is accepted: measured out of tree and recorded in the
   target's header, NOT pinned here -- the two below are a sample of the
   family, not an enumeration.

--------
目标的形状索引常量还携带 [u0 = u8]，将形状的同态和证明等级折叠到环境类别的等级上。这是圆锥词汇的作用，而不是函子或 [Cone] 记录的作用：当形状的同态等级声明严格低于环境等级时，函子类型和 [Cone] 记录都可以形成，而 [cone_leg] 和 [IsLimitCone] 则各自被拒绝。这些与 RELATED 折叠相关的，是同一捐赠者家族 Structure/Limit/Initial.v 的头记录；那里轴是形状自身的同态与自身证明，并且它将 [IsALimit] 命名为第三个捐赠者。[IsALimit] 也是该轴上的捐赠者，[Limit]、[ConeIso] 和 [FCone] 也是如此，它们在这些等级下各自被拒绝，而 [vertex_obj] 被接受：从树外测量并记录在目标的头中，而不是固定在此——下面的两个是家族的示例，而不是枚举。
*)

Section ShapeUniverseProbe.

Universes jo jh jp vo vh vp.
Constraint jh < vh.

Context (Ju : Category@{jo jh jp}).
Context (Vu : Category@{vo vh vp}).

Check (obj[Ju]).
Check (obj[Vu]).
Check (Ju ⟶ Vu).

Context (Fu : Ju ⟶ Vu).

Check (@Cone Ju Vu Fu).
Check (@ACone Ju Vu).

Fail Check (@cone_leg Ju Vu Fu).
Fail Check (@IsLimitCone Ju Vu Fu).

End ShapeUniverseProbe.

(** ** Non-vacuity: the torsion-free abelian groups / ** 非空性：无挠阿贝尔群 *)

(*
[TorsionFree_Reflective] (Instance/Ab/TorsionFree.v) is a full
   reflective subcategory of [Ab], and [Ab] has a terminal object
   ([Ab_Terminal], Instance/Ab.v).  The empty diagram therefore has a
   limit downstairs, and Mac Lane's exercise produces one upstairs.

   The limit downstairs is built here rather than taken from
   [Terminal_Limit] (Structure/Limit/Terminal.v): that theorem is
   closed with [Qed], so its apex would not reduce and the readbacks below
   would say nothing.  The hand-built version is [Defined], and the
   created apex then reduces all the way to the quotient of the terminal
   abelian group by its torsion subgroup.

   The witness deliberately lives here rather than in the target, so that
   [Instance/Ab] stays out of the target's dependency closure.

--------
[TorsionFree_Reflective]（实例/Ab/TorsionFree.v）是 [Ab] 的一个完全反射子范畴，而 [Ab] 有一个终对象（[Ab_Terminal]，实例/Ab.v）。因此，空图下方有一个极限，而 Mac Lane 的练习在上方产生一个极限。

下方的极限是在这里构建的，而不是从 [Terminal_Limit]（结构/极限/终对象.v）获取：该定理在 [Qed] 内是封闭的，因此其顶点不会简化，下面的回读将没有结果。手工构建的版本是 [Defined]，然后创建的顶点可以一直简化到终阿贝尔群对其扭子子群的商。

该证据故意存在于这里而不是在目标里，这样 [Instance/Ab] 就不会进入目标的依赖闭包。
*)

Definition probe_KAb : 0 ⟶ Sub Ab TorsionFree_Sub :=
  From_0 (Sub Ab TorsionFree_Sub).

Definition probe_ab_cone : Cone (Incl Ab TorsionFree_Sub ◯ probe_KAb).
Proof.
  unshelve refine {| vertex_obj := @terminal_obj Ab Ab_Terminal |}.
  unshelve econstructor; intro x; inversion x.
Defined.

Definition probe_ab_limit : Limit (Incl Ab TorsionFree_Sub ◯ probe_KAb).
Proof.
  unshelve refine {| limit_cone := probe_ab_cone |}.
  intro N.
  unshelve econstructor.
  - exact (@one Ab Ab_Terminal _).
  - intro x; inversion x.
  - intros v Hv; apply (@one_unique Ab Ab_Terminal).
Defined.

Example probe_ab_limit_apex :
  vertex_obj[@limit_cone _ _ _ probe_ab_limit]
    = @terminal_obj Ab Ab_Terminal := eq_refl.

Definition probe_ab_created : Limit probe_KAb :=
  reflective_inherits_limits TorsionFree_Reflective probe_KAb probe_ab_limit.

(* The created cone IS the lift of the cone downstairs ... / 所创建的圆锥是楼下圆锥的提升... *)

Example probe_ab_created_cone :
  @limit_cone _ _ _ probe_ab_created
    = reflective_lift TorsionFree_Reflective probe_KAb probe_ab_cone
  := eq_refl.

(* ... its apex IS the reflector applied to the terminal object ... / ... 它的顶点是应用于终对象的反射器 ... *)

Example probe_ab_created_apex :
  vertex_obj[@limit_cone _ _ _ probe_ab_created]
    = fobj[reflector TorsionFree_Reflective] (@terminal_obj Ab Ab_Terminal)
  := eq_refl.

(*
... and the created apex's carrier is the torsion quotient.  Read that
   at its strength: [torsion_reflector_obj] (Instance/Ab/TorsionFree.v)
   holds at an ARBITRARY object, so this readback pins the definitional
   unfolding of the reflector's object action and not that the reflection
   did anything here -- the terminal group is itself torsion-free, so the
   reflection is inert up to isomorphism, and the shape being [0] means
   every leg condition is exercised at no index at all ([IsLimitCone] at
   the empty shape is terminality).  The witness shows the assembly runs
   end to end and reduces, not that it is non-degenerate.

--------
... 创建的顶点的载体是挠商。在它的强度下读取它：[torsion_reflector_obj]（实例/Ab/无挠.v）在任意对象上成立，因此这个回读固定了反射器对象作用的定义性展开，而不是说反射在这里做了什么——终端群本身是无挠的，所以反射在同构下是惰性的，并且形状为 [0] 意味着每个腿条件在根本没有索引的情况下都被施加（[IsLimitCone] 在空形状下是终端性）。证据表明该组装从头到尾运行并简化，而不是它是非退化的。
*)

Example probe_ab_created_carrier :
  `1 (vertex_obj[@limit_cone _ _ _ probe_ab_created])
    = AbModTorsion (@terminal_obj Ab Ab_Terminal) := eq_refl.

(*
The subcategory is complete as soon as [Ab] is; no completeness
   witness for [Ab] is claimed here, so this is a conditional.

--------
子类别在 [Ab] 完成时即为完整；此处未声明 [Ab] 的完整性见证，因此这是有条件的。
*)

Check (reflective_Complete TorsionFree_Reflective).
