(**
* Probe for Structure/Limit/Comparison.v (issue #419)

    Pins the measured boundaries of the comparison-arrow development: which
    repackagings hold by conversion and which do not, that the
    discrete-diagram functor no longer pins the universe (§B, a repair
    recorded under N2/N3 below), how the terminal comparison is oriented,
    and why the colimit block is built directly.  Every
    refutation command below was stripped ONE AT A TIME in a copy of the
    whole file and compiled alone with its error read, so each refusal is
    of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   a twice-reindexed cone, of type
                     [Cone ((F ◯ W) ◯ V)], is not a [Cone (F ◯ (W ◯ V))]
                     by conversion (a has-type mismatch between the two
                     bracketings, no universe clause); [cone_assoc]
                     repackages it (control), and apex and legs agree at
                     [eq_refl] across the bracketings (readbacks).
     N2, N3          REPAIRED, and recorded as a correction.  An earlier
                     revision read:
                       "N2 UNIVERSE  under [Constraint Set < uh],
                        [cone_comparison] at the UNANNOTATED
                        [DiscreteCat_Functor] is refused: the functor's
                        type names [DiscreteCat@{_ Set Set}] where the
                        ambient's [uh] is needed; the cone type alone is
                        formable (control a), the comparison at the
                        annotated [DiscreteCat_Functor'] is accepted
                        (control b), and so is [binary_comparison]
                        (control c).
                        N3 UNIVERSE  the same pin reached through
                        Structure/Limit/Product.v's [family_cone], which
                        is built over the unannotated functor."
                     [DiscreteCat_Functor] was annotated in place in the
                     PR "algebraic carriers are sets" (2026-09-17),
                     Instance/Discrete.v, with exactly the binders
                     [DiscreteCat_Functor'] already carried; both
                     commands are now ACCEPTED and are kept in §B as
                     positive controls beside their former controls.
                     [DiscreteCat_Functor'] is now a transparent alias of
                     [DiscreteCat_Functor], so control (b) and the former
                     N2 are the same statement twice, which is the point:
                     the two names agree.  No UNIVERSE refusal remains in
                     this file.
     N4 TYPING       [to fobj_one_iso] has type [1 ~> F 1], not
                     [F 1 ~> 1]: the comparison is the class's [from]
                     (control), and [terminal_comparison_one] reads it as
                     the unique map into [1] (readback).
     N5 TYPING       [cone_comparison (F^op) N HM], with [HM] a colimiting
                     cocone of [F ◯ K], is refused with the clause "cannot
                     unify Cone (F^op ◯ K^op) and Cone (F ◯ K)^op"; once
                     [islimitcone_op_comp] repackages [HM] it is accepted
                     (control), as is [cocone_comparison] (control).

    Readbacks at [eq_refl]: [pullback_comparison] IS [cone_comparison];
    the components of [const_image_iso] are identities; reindexing along
    [Id] keeps the legs.  Positive formability of the two headline
    biconditionals and of the bundled limit and colimit biconditionals.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain tokenization, being the keyword itself, the
    two binder names [b] and [pi] that only the former N3 introduces, and
    the instrument's absent name — so a renamed or removed constant breaks the
    build on a positive line rather than letting a refutation pass for the
    wrong reason.

--------
* 用于结构/限制/比较的探针.v（问题 #419）

固定比较箭头开发的测量边界：哪些重打包通过转换保持，哪些不保持，离散图函子不再固定宇宙 (§B，下文 N2/N3 记录了修复)，终端比较的方向，以及为什么余极块是直接构建的。下面的每个反驳命令都是在整个文件的副本中一次移除一个，并单独编译，其错误被读取，因此每个拒绝都是其标签所说明的类型。

编号：
     工具      一个缺失的名称，被拒绝——反驳关键字是在此文件中存在。N1 转换   一个经过两次重新索引的锥体，类型为 [Cone ((F ◯ W) ◯ V)]，不是 [Cone (F ◯ (W ◯ V))]
     通过转换（两种括号之间存在类型不匹配，没有宇宙条款）；[cone_assoc]
     对其重新打包（控制），顶点和腿在括号之间（回读）在 [eq_refl] 上一致。N2、N3          已修复，并记录为更正。
早期的修订版本写道：
“N2 UNIVERSE 在 [Constraint Set < uh] 下，
[cone_comparison] 在未注释的 [DiscreteCat_Functor] 被拒绝：函子类型命名为 [DiscreteCat@{_ Set Set}]，而环境的 [uh] 是需要的；仅锥形类型是可形成的（控制 a），在注释的 [DiscreteCat_Functor'] 的比较被接受（控制 b），[binary_comparison] 也同样被接受（控制 c）。
N3 UNIVERSE 同一个引脚通过 Structure/Limit/Product.v 的 [family_cone] 到达，该引脚建立在未注释的函子之上。[DiscreteCat_Functor] 已在 PR “代数载体是集合”（2026-09-17）、Instance/Discrete.v 中进行了原位注释，带有 [DiscreteCat_Functor'] 已经携带的完全相同的绑定器；这两个命令现在都被接受，并作为正控制保存在 §B 中，旁边是它们以前的控制。[DiscreteCat_Functor'] 现在是 [DiscreteCat_Functor] 的透明别名，因此控制 (b) 和以前的 N2 是同一个语句两次，这就是重点：这两个名称一致。此文件中不再存在 UNIVERSE 拒绝。
N4 类型       [to fobj_one_iso] 的类型是 [1 ~> F 1]，而不是 [F 1 ~> 1]：比较的是类的 [from]（控制），而 [terminal_comparison_one] 将其读取为进入 [1] 的唯一映射（读回）。 N5 类型       [cone_comparison (F^op) N HM]，其中 [HM] 是 [F ◯ K] 的一个余极限余锥，在条款“无法统一 Cone (F^op ◯ K^op) 和 Cone (F ◯ K)^op”下被拒绝；一旦 [islimitcone_op_comp] 重新打包 [HM]，就被接受（控制），[cocone_comparison] 也同样被接受（控制）。

在 [eq_refl] 上的回读：[pullback_comparison] 是 [cone_comparison]；
[const_image_iso] 的组成部分是恒等式；沿 [Id] 重新索引保持了各分支。两个标题双条件语句以及捆绑的极限和余极限双条件语句具有正形成性。

守卫覆盖：每一个被反驳命名的常量也在反驳命令之外被命名（位于末尾的守卫块）——在普通的标记化下的例外是关键字本身、两个绑定器名称 [b] 和 [pi]（只有前者 N3 引入），以及工具缺失的名称——因此，重命名或移除一个常量会在正面行上导致构建失败，而不是让反驳因为错误的原因通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Span.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Structure.Limit.Comparison.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe419_absent_name.

(** ** A: the two bracketings of a twice-reindexed cone are distinct types / ** A: the two bracketings of a twice-reindexed cone are distinct types / ** A：经过两次重新索引的圆锥的两个括号形式是不同的类型 *)

Section Bracketing.

Context {J'' J' J C : Category} (W : J' ⟶ J) (V : J'' ⟶ J') {F : J ⟶ C}.

(* control: at its own bracketing / 控制：在其自身的括号内 *)
Check (fun N : Cone F =>
         (cone_reindex V (cone_reindex W N) : Cone ((F ◯ W) ◯ V))).

(* control: repackaged field by field, it is a cone at the other one / control: repackaged field by field, it is a cone at the other one / 控制：逐字段重新打包，它在另一个上是一个圆锥 *)
Check (fun N : Cone F =>
         (cone_assoc (cone_reindex V (cone_reindex W N)) : Cone (F ◯ (W ◯ V)))).

(* N1 CONVERSION: not by conversion / N1 转换：不是通过转换 *)
Fail Check (fun N : Cone F =>
              (cone_reindex V (cone_reindex W N) : Cone (F ◯ (W ◯ V)))).

(* readbacks: apex and legs agree at [eq_refl] across the two bracketings / 回读：Apex 和腿在两个括号中于 [eq_refl] 一致 *)
Check (@cone_reindex_comp_apex J'' J' J C W V F).
Check (@cone_reindex_comp_leg J'' J' J C W V F).

End Bracketing.

(** ** B: the former [Set] pin of the discrete-diagram functor, lifted / ** B：离散图示函子以前的 [Set] 引脚，被提升 *)

Section SetPin.

Universe uo uh.
Constraint Set < uh.

Context (Cu Du : Category@{uo uh uh}) (Fu : Cu ⟶ Du) (fam : bool → Cu)
        (HC : @Cartesian Cu) (HD : @Cartesian Du).

(* control (a): the cone type over the unannotated functor is formable / 控制 (a)：未标注函子的圆锥类型是可构造的 *)
Check (fun N : Cone (@DiscreteCat_Functor bool Cu fam) => N).

(* control (b): the comparison at the annotated functor / 控制 (b)：注释函数的比较 *)
Check (fun (N : Cone (@DiscreteCat_Functor' bool Cu fam))
           (M : Cone (Fu ◯ @DiscreteCat_Functor' bool Cu fam))
           (HM : IsLimitCone M) =>
         cone_comparison Fu N HM).

(* control (c): the elementary binary comparison / 控制 (c)：基本的二进制比较 *)
Check (@binary_comparison Cu Du Fu HC HD fam).

(*
Former N2, now a positive control: the comparison at the annotated
   functor.  RECORDED CORRECTION -- see the header.

--------
前 N2，现在是阳性对照：在注释的泛函上的比较。已记录更正——见标题。
*)
Check (fun (N : Cone (@DiscreteCat_Functor bool Cu fam))
                (M : Cone (Fu ◯ @DiscreteCat_Functor bool Cu fam))
                (HM : IsLimitCone M) =>
              cone_comparison Fu N HM).

(*
Former N3, now a positive control: Structure/Limit/Product.v's
   [family_cone] feeds it too.  RECORDED CORRECTION -- see the header.

--------
前 N3，现在是阳性对照：Structure/Limit/Product.v 的 [family_cone] 也给它供电。已记录的更正——见标题。
*)
Check (fun (c : Cu) (pi : ∀ b : bool, c ~{Cu}~> fam b)
                (M : Cone (Fu ◯ @DiscreteCat_Functor bool Cu fam))
                (HM : IsLimitCone M) =>
              cone_comparison Fu (family_cone fam c pi) HM).

End SetPin.

(** ** C: the orientation of [TerminalFunctor]'s comparison / ** C：[TerminalFunctor] 比较的方向 *)

Section Orientation.

Context {C D : Category} (F : C ⟶ D) `{@Terminal C} `{@Terminal D}.

(* control: the comparison direction is the class's [from] / 控制：比较方向是类的 [from] *)
Check (fun HF : @TerminalFunctor C D F _ _ =>
         (from (@fobj_one_iso _ _ F _ _ HF) : F terminal_obj ~{D}~> terminal_obj)).

(* N4 TYPING: [to] is oriented the other way / N4 输入：[to] 方向相反 *)
Fail Check (fun HF : @TerminalFunctor C D F _ _ =>
              (to (@fobj_one_iso _ _ F _ _ HF) : F terminal_obj ~{D}~> terminal_obj)).

(* readback: the comparison is the unique map into [1] / 回读：比较是映射到 [1] 的唯一映射 *)
Check (terminal_comparison_one F nullary_fam).

End Orientation.

(** ** D: the limit comparison does not read a cocone without repackaging / ** D: the limit comparison does not read a cocone without repackaging / ** D：极限比较不会在不重新包装的情况下读取余锥 *)

Section OpRoute.

Context {J C D : Category} {K : J ⟶ C} (F : C ⟶ D).

(* control: the cocone comparison / 控制：可可恩比较 *)
Check (fun (N : Cocone K) (M : Cocone (F ◯ K)) (HM : IsColimitCocone M) =>
         cocone_comparison F N HM).

(* control: the op route, once [M] is repackaged by [cone_op_comp] / 控制：操作路线，一旦 [M] 被 [cone_op_comp] 重新打包 *)
Check (fun (N : Cocone K) (M : Cocone (F ◯ K)) (HM : IsColimitCocone M) =>
         cone_comparison (F^op) N (islimitcone_op_comp HM)).

(* N5 TYPING: the op route on the cocone as it stands / N5 打字：就目前而言，cocone 上的操作路线 *)
Fail Check (fun (N : Cocone K) (M : Cocone (F ◯ K)) (HM : IsColimitCocone M) =>
              cone_comparison (F^op) N HM).

End OpRoute.

(** ** E: readbacks and positive formability / ** E：回读和正向可成型性 *)

Example p419_pullback_is {C D : Category} (H : C ⟶ D) (F : Cospan C)
  (N : Cone F) {M : Cone (H ◯ F)} (HM : IsLimitCone M) :
  pullback_comparison H F N HM = cone_comparison H N HM := eq_refl.

Example p419_const_component {J C D : Category} (F : C ⟶ D) (c : C) (x : J) :
  to (`1 (@const_image_iso J C D F c) x) = id[F c] := eq_refl.

Example p419_reindex_id_leg {J C : Category} {F : J ⟶ C} (N : Cone F) (j : J) :
  cone_leg (cone_reindex Id[J] N) j = cone_leg N j := eq_refl.

Check (fun (C D : Category) (F : C ⟶ D) (HC : @Cartesian C) (HD : @Cartesian D) =>
         @cartesian_functor_iff_preserves_binary_products C D F HC HD).

Check (fun (C D : Category) (F : C ⟶ D) (HC : @Terminal C) (HD : @Terminal D) =>
         @terminal_functor_iff_preserves_terminal C D F HC HD).

Check (fun (J C D : Category) (K : J ⟶ C) (F : C ⟶ D) (M : Cone (F ◯ K))
           (HM : IsLimitCone M) =>
         preserves_iff_comparison_iso F HM).

Check (fun (J C D : Category) (K : J ⟶ C) (F : C ⟶ D) (M : Cocone (F ◯ K))
           (HM : IsColimitCocone M) =>
         preserves_colimit_iff_comparison_iso F HM).

(** ** Guard block / ** 防守格挡 *)

Check @cone_reindex.
Check @cone_reindex_apex.
Check @cone_reindex_leg.
Check @cone_reindex_id_apex.
Check @cone_reindex_id_leg.
Check @cone_reindex_comp_apex.
Check @cone_reindex_comp_leg.
Check @reindex_comparison.
Check @reindex_comparison_commutes.
Check @reindex_comparison_unique.
Check @reindex_comparison_iso.
Check @reindex_comparison_iso_LimitCone.
Check @preserves_iff_comparison_iso.
Check @PreservesLimitCone_of_cone.
Check @PreservesLimitCone_of_comparison_iso.
Check @colimitcocone_iso.
Check @cocone_comparison_commutes.
Check @cocone_comparison_unique.
Check @ColimitCocone_comparison_iso.
Check @comparison_iso_ColimitCocone.
Check @PreservesColimitCocone_of_comparison.
Check @comparison_iso_of_PreservesColimitCocone.
Check @preserves_colimit_iff_comparison_iso.
Check @const_image_iso.
Check @const_image_iso_component.
Check @pullback_comparison.
Check @pullback_comparison_is.
Check @rapl_comparison_iso.
Check @DiscreteCat_Functor'.
Check @discrete_cone.
Check @discrete_cone_leg.
Check @discrete_IsLimitCone_of_IsIndexedProduct.
Check @discrete_IsIndexedProduct_of_IsLimitCone.
Check @binary_proj.
Check @IsIndexedProduct_binary.
Check @binary_fam.
Check @binary_cone.
Check @binary_cone_IsLimitCone.
Check @binary_image_cone.
Check @binary_image_cone_IsLimitCone.
Check @binary_comparison.
Check @binary_comparison_exl.
Check @binary_comparison_exr.
Check @binary_comparison_fork.
Check @cartesian_functor_iff_comparison_iso.
Check @cartesian_functor_iff_preserves_binary_products.
Check @nullary_proj.
Check @IsIndexedProduct_nullary.
Check @nullary_fam.
Check @nullary_cone.
Check @nullary_cone_IsLimitCone.
Check @nullary_image_cone.
Check @nullary_image_cone_IsLimitCone.
Check @terminal_comparison.
Check @terminal_comparison_one.
Check @terminal_functor_iff_comparison_iso.
Check @terminal_functor_iff_preserves_terminal.
Check @cone_assoc.
Check @cone_comparison.
Check @cocone_comparison.
Check @islimitcone_op_comp.
Check @DiscreteCat_Functor.
Check @family_cone.
Check @fobj_one_iso.
Check @TerminalFunctor.
Check @IsLimitCone.
Check @IsColimitCocone.
Check @Cone.
Check @Cocone.
Check @Cospan.
Check @Cartesian.
Check @Terminal.
Check @terminal_obj.
Check @cone_leg.
Check @vertex_obj.
Check @to.
Check @from.
Check @id.
