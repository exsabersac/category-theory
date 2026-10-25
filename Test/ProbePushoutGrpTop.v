Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Pushout.

Generalizable All Variables.

(** * Probe: the strength boundary of the Grp and Top pushouts / * 探测：Grp 和 Top 推出中的强度边界 *)

(*
Guard file for Instance/Grp/Pushout.v and Instance/Top/Pushout.v, in
   the Test/ProbeFunnyPoly.v convention.  Every negative is paired with a
   positive control that NAMES ITS OWN CONSTANTS, so that a rename or a
   definitional change breaks this file loudly instead of turning a [Fail]
   vacuously green.  The pairing was verified by RENAME SIMULATION: each
   negative was copied to a scratch file with one constant renamed, and
   the scratch file was confirmed to stop compiling.

   The import list is the UNION of the two targets' import lists, in
   dependency order -- a short prefix is what makes probes pass for the
   wrong reason.

   Conversion negatives ([Fail Definition ... := eq_refl]) and formability
   negatives ([Fail Check ...]) are kept in separate sections; they fail
   for different reasons and must not be read as one kind.  (Since #450 the
   formability section holds controls only: its two negatives recorded a
   donor pin that #450 lifted, and its correction says so.)  Each negative
   was stripped of its [Fail] once and the resulting message inspected;
   the kind is recorded beside it.

--------
Instance/Grp/Pushout.v 和 Instance/Top/Pushout.v 的保护文件，遵循 Test/ProbeFunnyPoly.v 的惯例。每个负例都配有一个正向控制，该控制会命名其自己的常量，因此重命名或定义更改会明显破坏此文件，而不是使 [Fail] 空泛地通过。通过重命名模拟验证了这种配对：每个负例都被复制到一个草稿文件中，并对其中的一个常量进行了重命名，确认该草稿文件无法继续编译。

导入列表是两个目标的导入列表的并集，按依赖顺序排列——一个短前缀就是让探测因错误的原因通过的原因。

转换缺陷（[Fail Definition ... := eq_refl]）和可成形性缺陷（[Fail Check ...]）保存在不同的部分；它们失败的原因不同，不能视为同一种类。（自#450以来，可成形性部分只保留控制项：它的两个缺陷记录了一个#450移除的捐赠针，并且其更正说明了这一点。）每个缺陷都去掉过一次其[Fail]，并检查了产生的消息；缺陷类型记录在其旁边。
*)

(**
** Instrument check

    A [Fail] that must itself fail, so that a globally broken [Fail]
    vernacular would be caught here rather than silently greening the
    negatives below.

--------
** 仪器检查

    一个必须自身失败的 [Fail]，这样一个全局损坏的 [Fail]
    术语将在此处被捕获，而不是在下面的负面结果中默默显示为绿色。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Positive controls, and conversion negatives / ** 阳性对照和转换阴性 *)

Section GrpConversion.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).
Context {Q : GrpObject}.
Context (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q).
Context (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g).

(*
CONTROL 1.  The chosen pushout's apex and first injection ARE the
   hand-built ones; the record projections reduce.

--------
控制 1. 所选推出的顶点和第一个注入是手工构建的；记录投影会减少。
*)
Definition ctl_grp_apex :
  pushout_apex (Grp_pushout f g) = AmalgamGrp f g := eq_refl.

Definition ctl_grp_in1 :
  pushout_in1 (Grp_pushout f g) = am_inj1 f g := eq_refl.

(*
CONTROL 2.  The mediator's own value on the three formers reduces --
   [am_eval] is a [Fixpoint], so this is where [am_med]'s homomorphism
   laws come from.

--------
控制 2. 调解者在前三个上的自身值减少——
[am_eval] 是一个 [Fixpoint]，所以这就是 [am_med] 同态律的来源。
*)
Definition ctl_grp_med_unit :
  grp_map (am_med f g q1 q2 Hcomm) am_one = grp_unit Q := eq_refl.

Definition ctl_grp_med_mul (u v : AmTerm B C) :
  grp_map (am_med f g q1 q2 Hcomm) (am_mul u v)
    = grp_mul Q (grp_map (am_med f g q1 q2 Hcomm) u)
                (grp_map (am_med f g q1 q2 Hcomm) v) := eq_refl.

(*
CONTROL 2b.  [pushout_med] itself is named in a control, so that
   renaming it breaks this file rather than turning NEGATIVE 1 vacuously
   green -- [Fail] catches "reference not found" just as happily as it
   catches a unification failure.

--------
控制 2b。[pushout_med] 本身在一个控制中被命名，因此重命名它会破坏此文件，而不是使 NEGATIVE 1 无意义地变为绿色 —— [Fail] 捕捉“未找到引用”就像它捕捉合并失败一样有效。
*)
Definition ctl_grp_med_typed
  : pushout_apex (Grp_pushout f g) ~{Grp}~> Q :=
  pushout_med (Grp_pushout f g) Hcomm.

(*
NEGATIVE 1 (conversion).  [pushout_med] does NOT reduce to [am_med].
   Stripping the [Fail] reports a unification failure between
   [unique_obj (pushout_ump ...)] and [am_med ...].  The cause is DONOR
   OPACITY and not this file's construction: Structure/Pushout.v states
   [pushout_ump] as a [Lemma ... Qed], so [unique_obj] is applied to an
   opaque constant and no amount of transparency here would help.
   Instance/Grp/Pushout.v's [Grp_pushout_med_is_am_med] is the [≈] form
   that does hold.

--------
负面 1（转换）。[pushout_med] 不会化简为 [am_med]。去掉 [Fail] 会导致 [unique_obj (pushout_ump ...)] 与 [am_med ...] 之间的统一失败。原因是捐赠者的不透明性，而不是该文件的构建问题：Structure/Pushout.v 声明 [pushout_ump] 为 [Lemma ... Qed]，因此 [unique_obj] 被应用于一个不透明常量，在这里任何程度的透明化都无济于事。Instance/Grp/Pushout.v 的 [Grp_pushout_med_is_am_med] 是确实成立的 [≈] 形式。
*)
Fail Definition neg_grp_med :
  pushout_med (Grp_pushout f g) Hcomm = am_med f g q1 q2 Hcomm := eq_refl.

End GrpConversion.

Section TopConversion.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).
Context {Q : TopSpace}.
Context (q1 : B ~{Top}~> Q) (q2 : C ~{Top}~> Q).
Context (Hcomm : q1 ∘[Top] f ≈ q2 ∘[Top] g).

(* CONTROL 3.  Same reduction on the Top side. / 控制 3。顶部同样减小。 *)
Definition ctl_top_apex :
  pushout_apex (Top_pushout f g) = Pushout_Top f g := eq_refl.

Definition ctl_top_in1 :
  pushout_in1 (Top_pushout f g) = Top_po_in1 f g := eq_refl.

(*
CONTROL 3b.  Names [pushout_med] and [Top_po_med], for the same
   pairing reason.

--------
控制 3b。 名称 [pushout_med] 和 [Top_po_med]，出于相同配对原因。
*)
Definition ctl_top_med_typed
  : pushout_apex (Top_pushout f g) ~{Top}~> Q :=
  pushout_med (Top_pushout f g) Hcomm.

Definition ctl_top_med_named
  : Pushout_Top f g ~{Top}~> Q := Top_po_med f g q1 q2 Hcomm.

(*
NEGATIVE 2 (conversion).  The SAME donor opacity, on the other
   substrate -- which is what shows the cause is Structure/Pushout.v's
   [Qed] rather than anything about groups.

--------
NEGATIVE 2（转换）。相同的供体不透明度，在另一个基板上——这表明原因是 Structure/Pushout.v 的 [Qed]，而不是关于组的任何内容。
*)
Fail Definition neg_top_med :
  pushout_med (Top_pushout f g) Hcomm = Top_po_med f g q1 q2 Hcomm := eq_refl.

End TopConversion.

Section TopEmptySpan.

Context (B C : TopSpace).

Notation Ef := (top_zero B).
Notation Eg := (top_zero C).

(*
CONTROL 4.  The POINTS of the empty-span pushout are the coproduct's
   points on the nose.

--------
控制 4。空跨度推挤的点恰好是余积的点。
*)
Definition ctl_top_points :
  carrier (top_carrier (Pushout_Top Ef Eg))
    = carrier (sum_carrier B C) := eq_refl.

(*
NEGATIVE 3 (conversion).  The SETOIDS differ, so the two
   [SetoidObject]s are not convertible: the pushout apex compares points
   by the inductive [tp_rel], the coproduct by [sum_setoid]'s [match].
   Stripping the [Fail] reports "cannot unify
   "top_carrier (Pushout_Top Ef Eg)" and "sum_carrier B C"" -- it
   names no field; that the difference is confined to the setoid is a
   DIAGNOSIS, supported by [ctl_top_points] showing the carriers agree.
   This is what makes [Top_pushout_empty_iso] a genuine
   isomorphism rather than an identity.

--------
否定 3（转换）。SETOIDS 不同，因此两个 [SetoidObject] 不能互相转换：推顶点通过归纳 [tp_rel] 比较点，余积通过 [sum_setoid] 的 [match] 比较点。剥离 [Fail] 报告“无法统一‘top_carrier (Pushout_Top Ef Eg)’和‘sum_carrier B C’”——它没有命名任何字段；差异仅限于 setoid，这是一个诊断（DIAGNOSIS），由 [ctl_top_points] 支持，显示承载体一致。这就是使 [Top_pushout_empty_iso] 成为真正同构而非恒等的原因。
*)
Fail Definition neg_top_carrier :
  top_carrier (Pushout_Top Ef Eg) = sum_carrier B C := eq_refl.

(*
CONTROL 4b.  Names [IsOpen] and [Sum_Top], which NEGATIVE 4 mentions
   and no other control did.

--------
控制 4b。名称 [IsOpen] 和 [Sum_Top]，是 NEGATIVE 4 提到的，而其他对照没有提到。
*)
Definition ctl_top_sum_open (W : sum_carrier B C → Type)
  (H : IsOpen (Sum_Top B C) W) : IsOpen (Sum_Top B C) W := H.

(*
NEGATIVE 4 (conversion).  The TOPOLOGIES differ too: [tp_open] carries
   a respect-the-gluing clause that [sum_open] does not.  Over the empty
   span that clause is redundant -- which is exactly what
   [Top_pushout_empty_iso] proves -- but it is not definitionally
   absent.

--------
负四（转换）。拓扑结构也不同：[tp_open] 包含一个尊重粘合的条款，而 [sum_open] 没有。在空跨度上，该条款是多余的——这正是 [Top_pushout_empty_iso] 证明的——但它在定义上并不缺失。
*)
Fail Definition neg_top_topology :
  IsOpen (Pushout_Top Ef Eg) = IsOpen (Sum_Top B C) := eq_refl.

End TopEmptySpan.

(**
** Formability: a donor [Set] pin, since lifted, and the route around it

    CORRECTION (#450).  This section was written when [Instance/Grp.v]'s
    [Grp_zero_hom] was declared over [GrpObject@{Set Set Set}] -- a DONOR
    pin, of the same family that Instance/Grp/Quotient/Colimit.v recorded
    for [Grp_trivial] and [Grp_Zero] -- and its NEGATIVES 5 and 6 were that
    donor's rejection above [Set].  #450 annotated the donor's universes in
    place ([Grp_trivial@{p} : GrpObject@{p p p}],
    [Grp_zero_hom@{u p}], [Grp_Zero@{u p}]; the essay above [Grp_trivial]
    in Instance/Grp.v has the readbacks), after which both guarded [Check]s
    below stopped being refused: the build stopped at the first of them
    with Rocq's report that the guarded command had been accepted.  They
    are kept, without the guard, as
    CONTROLS 9 and 10, so that the lifted pin is guarded in the other
    direction.  What the section still establishes is that
    Instance/Grp/Pushout.v's free product, along the CONSTANT legs, was
    formable above [Set] before the lift as well as after it.

--------
** 可成型性：一个捐赠的 [Set] 引脚，自被抬起以来，以及绕过它的路径

更正 (#450)。本节的编写时间是在 [Instance/Grp.v] 的 [Grp_zero_hom] 被宣告高于 [GrpObject@{Set Set Set}] —— 一个 DONOR 引脚，属于 Instance/Grp/Quotient/Colimit.v 为 [Grp_trivial] 和 [Grp_Zero] 记录的同一家族 —— 并且其 NEGATIVES 5 和 6 是那位捐赠者对 [Set] 之上的拒绝。#450 在原位标注了捐赠者的宇宙 ([Grp_trivial@{p} : GrpObject@{p p p}]、[Grp_zero_hom@{u p}]、[Grp_Zero@{u p}]；Instance/Grp.v 中 [Grp_trivial] 之上的文章有读取回溯)，之后下面的两个受保护的 [Check] 不再被拒绝：构建在它们中的第一个处停止，并有 Rocq 报告称受保护的命令已被接受。它们在去掉保护后作为 CONTROLS 9 和 10 保留，以便升起的引脚在另一方向上受到保护。本节仍然确立的是，Instance/Grp/Pushout.v 的自由积沿着 CONSTANT 端，在升起之前以及之后，都可以在 [Set] 之上形成。
*)

Section SetPin.

Universe bg.
Constraint Set < bg.

(*
CONTROL 5.  The amalgamated product is formable strictly above [Set]:
   no [Set] pin anywhere in the pushout proper.

--------
控制 5. 合金化产品只能在 [Set] 以上形成：在推送部分的任何位置都没有 [Set] 引脚。
*)
Check (fun (A B C : GrpObject@{bg bg bg})
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) => AmalgamGrp f g).

(* CONTROL 6.  So is the chosen pushout, hence [Grp_HasPushouts]. / 控制 6。因此是选定的推断，因此 [Grp_HasPushouts]。 *)
Check (fun (A B C : GrpObject@{bg bg bg})
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) =>
         pushout_apex (Grp_pushout f g)).

(*
CONTROL 7.  And so are the free product and its injection -- this is
   the route-around, and it was the contrast to the two negatives that
   stood below until #450 (CONTROLS 9 and 10 since).  [grp_const] is
   named too, being what makes it work.

--------
控制 7。自由产品及其注射也是如此——这是绕行的方法，并且它与下面的两个阴性形成了对比，直到 #450（随后是控制 9 和 10）。[grp_const] 也被命名，它是使其起作用的原因。
*)
Check (fun B C : GrpObject@{bg bg bg} => Grp_free_product B C).
Check (fun B C : GrpObject@{bg bg bg} => Grp_fp_inl B C).
Check (fun B C : GrpObject@{bg bg bg} => grp_const B C).

(*
CONTROL 8.  The donor constants exist and are usable at [Set]-level
   groups.

--------
控制8。供体常数存在并可在 [Set] 级别组中使用。
*)
Check (Grp_zero_hom Z2).
Check (Grp_zero_hom_Section Z2).

(*
CONTROL 9, formerly NEGATIVE 5 (formability).  Before #450,
   Instance/Grp.v's map out of the trivial group was NOT formable above
   [Set], and stripping the guard reported "Cannot enforce Set = bg".
   Since #450 it is formable at every carrier level.

--------
CONTROL 9，前称 NEGATIVE 5（可形成性）。在 #450 之前，实例/组的映射出平凡群在 [Set] 之上不可形成，并且去掉保护时报告“无法强制执行 Set = bg”。自 #450 之后，它在每个承载层次上都是可形成的。
*)
Check (fun G : GrpObject@{bg bg bg} => Grp_zero_hom G).

(*
CONTROL 10, formerly NEGATIVE 6 (formability).  Hence so is the
   splitting of that map.  Instance/Grp/Pushout.v still builds the free
   product along the constant legs, not on [Grp_zero_hom_Section]; its
   header records why that choice no longer rests on the pin.

--------
CONTROL 10，前称 NEGATIVE 6（可形成性）。因此，该映射的分裂也是如此。Instance/Grp/Pushout.v 仍然沿着恒定边构建自由积，而不是在 [Grp_zero_hom_Section] 上；其头文件记录了为何这一选择不再依赖于引脚。
*)
Check (fun G : GrpObject@{bg bg bg} => Grp_zero_hom_Section G).

End SetPin.
