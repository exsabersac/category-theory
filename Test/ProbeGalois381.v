(**
* Boundary probe for the group-action Galois connection (#381)

    This file exists for what an in-file [Fail] cannot do: survive a
    rename.  A negative written inside the module it guards is renamed in
    lockstep with the constant it names and so stays green when that
    constant disappears; a negative written HERE breaks loudly.

    The [Require] list below is the target's own list, plus the target.  A
    short prefix is exactly what makes a probe pass for the wrong reason
    -- a missing coercion or notation can turn an intended unification
    mismatch into an "illegal application" -- so the list is mirrored
    rather than trimmed.

    ** THE NEGATIVES, BY KIND

    Seven negatives plus one instrument check (six since #450; see the
    FORMABILITY paragraph).  The kinds are told apart
    by the error TEXT, not by a label, and every one was stripped ONE AT A
    TIME, compiled alone, and its whole error read.

      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and NO universe
                   clause.  Negative 2.  This is the content of Mac Lane's
                   display (1): the connection is [L X >= S], not
                   [L X <= S], so it does not inhabit the covariant
                   reading.

      CONVERSION   "cannot unify" between two inhabitants of ONE type, or
                   between two categories.  Negatives 3, 4 and 5.

      FORMABILITY  ends in "universe inconsistency: Cannot enforce ...".
                   Negatives 6, 7 and 8.  Within them the reported clause
                   separates two shapes: 6 and 7 are LEVEL rejections
                   between two DECLARED universes ("Cannot enforce qh = qo
                   because qo < qh"), while 8 reports the literal [Set]
                   ("Cannot enforce Set = ... because Set < ..."), which
                   is what made Instance/Grp.v's [Z2] unusable
                   here.  (CORRECTION, #450: Negative 8 is a CONTROL
                   since #450 wrote out [Z2]'s universes in place; see
                   its section.  Seven negatives are six since.)

    Every constant a negative names also appears in a command OUTSIDE any
    [Fail], donors included -- a guard that names a constant only inside
    its own [Fail] is vacuous, and the control block below was written by
    reading the [Fail] commands rather than from memory.

--------
* 用于群作用伽罗瓦连接的边界探针 (#381)

这个文件的存在是为了处理文件内部的 [Fail] 做不到的事情：在重命名时仍然存在。在它所保护的模块中写入的负值会随着它所命名的常量同步重命名，因此当该常量消失时仍保持绿色；而在这里写入的负值会大声报错。

下面的 [Require] 列表是目标本身的列表，加上目标本身。一个简短的前缀恰恰会让探针因为错误的原因通过——缺失的强制或符号注释可能会把预期的统一不匹配变成“非法应用”——所以列表是镜像的，而不是裁剪的。

** 负面因素，按种类

七个底片加一个仪器检查（自#450起为六个；参见可成型性段落）。这些类型是通过错误文本区分的，而不是通过标签，每一个都被一次剥离、单独编译，并读取其整个错误。

输入一个普通的“has type ... while it is expected to have type ...”，没有“cannot unify”且没有宇宙子句。负2。这是Mac Lane显示（1）的内容：连接是[L X >= S]，而不是[L X <= S]，因此它不属于协变的解读。

转换 “不能统一”在同一类型的两个元素之间，或在两个类别之间。 否定 3、4 和 5。

可塑性以“宇宙不一致：无法强制执行...”结束。
否定 6、7 和 8。在它们之中，报告的子句将两个形状分开：6 和 7 是两个声明的宇宙之间的 LEVEL 拒绝（“无法强制执行 qh = qo 因为 qo < qh”），而 8 报告了字面上的 [Set]（“无法强制执行 Set = ... 因为 Set < ...”），这就是使 Instance/Grp.v 的 [Z2] 在此不可用的原因。（更正，#450：否定 8 是一个 CONTROL，因为 #450 在原位写出了 [Z2] 的宇宙；见其章节。七个否定因此变为六个。）

每个常量一个负名称也出现在任何 [Fail] 之外的命令中，包括捐赠者——一个仅在其自身 [Fail] 内命名常量的保护是空的，下面的控制块是通过读取 [Fail] 命令而不是从内存中编写的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.Grp.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument / ** 负 1：仪器 *)

(*
If [Fail] were inert -- a missing scope, a stray [Set Silent] -- this
   would pass and every other negative below would be worthless.

--------
如果 [Fail] 是惰性的——一个缺失的范围，一个流落的 [Set Silent]——这将通过，而下面的每一个其他否定都将毫无意义。
*)
Fail Check probe381_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(** ** Controls for the constants the negatives name / ** 控制常数否定的名称 *)

Check @subset_le.
Check @subset_le_preorder.
Check @Subsets.
Check @op_rel.
Check @op_PreOrder.
Check @Proset.
Check @GaloisConnection.
Check @GrpObject.
Check @grp_setoid.
Check @MSetoidAction.
Check @act_setoid.
Check @grp_mon.
Check @Powerset_Prop_obj.
Check @Z2.
Check @AdjointOnTheRight.
Check @stab.
Check @fixed.
Check @stab_PreOrder_G.
Check @group_action_galois.
Check @group_action_adjunction.
Check @group_action_AdjointOnTheRight.
Check @stab_fixed_stab.
Check @fixed_stab_fixed.
Check @stab_Subgroup.
Check @closed_G_iff.
Check @closed_U_iff.
Check @ClosedG.
Check @ClosedU.
Check @subset_le_antisym.
Check @gal_lrl_below.
Check @gal_lrl_above.
Check @gal_closed_l_iff.
Check @StabOp.
Check @FixedOp.
Check @GalZ2.
Check @GalZ2Act.
Check @GalV4.
Check @GalV4Act.
Check @galois_two.
Check @galois_true.
Check @galois_stab_true_trivial.
Check @galois_v4_stab_proper.

(* ------------------------------------------------------------------------ *)
(** ** Negative 2 (TYPING): the connection is antitone, not covariant / ** 负2（打字）：连接是反变的，而不是协变的 *)

(*
Mac Lane's display (1) reads "L p >= q in Q", and the construction
   paragraph "L X >= S in Q".  Reading the second relation as plain
   inclusion instead of its reverse gives a term of the wrong TYPE: the
   error is a bare "has type ... while it is expected to have type ...",
   with no "cannot unify" and no universe clause.

--------
麦克·莱恩的展示（1）显示“L p >= q in Q”，而构造段落显示“L X >= S in Q”。如果将第二个关系读作普通包含而不是它的逆，会得到错误类型的项：错误是一个简单的“具有类型……而预期具有类型……”，没有“无法统一”也没有宇宙条款。
*)

Section AntitoneIsNotCovariant.

Universe po pgu.
Constraint Set < po.
Constraint po <= pgu.

(*
RE-MEASURED after the PR "algebraic carriers are sets" (2026-09-17).
   [GrpObject]'s [PropEquiv] field permuted its three universe roles from
   (carrier, proof, aux) to (aux, carrier, proof), so the SAME reading that
   an earlier revision spelled [GrpObject@{po po pgu}] is now
   [GrpObject@{pgu po po}]: [pgu] keeps its role, only its position moved.
   The constraints on this section are unchanged.

--------
在 PR “代数承载集合”（2026-09-17）之后重新测量。[GrpObject] 的 [PropEquiv] 字段将其三个宇宙角色从 (承载, 证明, 辅助) 调换为 (辅助, 承载, 证明)，所以之前版本拼写 [GrpObject@{po po pgu}] 的相同读法现在是 [GrpObject@{pgu po po}]：[pgu] 保持其角色，仅位置移动。本节的约束未改变。
*)
Context (Gp : GrpObject@{pgu po po}).
Context (Ap : MSetoidAction@{po po pgu pgu pgu po po pgu}
                (grp_mon@{pgu po po} Gp)).

(* The control: the connection DOES inhabit the antitone reading. / 控制：该连接确实存在反调性解读。 *)
Check (group_action_galois Gp Ap
        : GaloisConnection (@subset_le@{po} (act_setoid Ap))
            (op_rel (@subset_le@{po} (grp_setoid Gp)))).

Fail Check (group_action_galois Gp Ap
             : GaloisConnection (@subset_le@{po} (act_setoid Ap))
                 (@subset_le@{po} (grp_setoid Gp))).

(* ---------------------------------------------------------------------- *)
(** ** Negatives 3 and 4 (CONVERSION), stated in the same section / ** 同一部分中提到的第3和第4项负面（转换） *)

(*
Idempotence of the two closure operators holds at the carriers' own
   [equiv] and NOT at [eq_refl]: the two sides are different terms, and no
   amount of unfolding identifies a triple composite with a single one.

--------
两个闭包算子的幂等性在承载者自己的 [equiv] 上成立，而在 [eq_refl] 上不成立：两边是不同的项，任何展开都无法将三重复合体识别为单一的复合体。
*)

Check (fun X => stab_fixed_stab Gp Ap X
         : stab (fixed (stab X)) ≈ stab X).

Fail Check (fun (X : carrier (Powerset_Prop_obj@{po} (act_setoid Ap))) =>
              (eq_refl : @stab Gp Ap (@fixed Gp Ap (@stab Gp Ap X))
                           = @stab Gp Ap X)).

Check (fun S => fixed_stab_fixed Gp Ap S
         : fixed (stab (fixed S)) ≈ fixed S).

Fail Check (fun (S : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp))) =>
              (eq_refl : @fixed Gp Ap (@stab Gp Ap (@fixed Gp Ap S))
                           = @fixed Gp Ap S)).

(* ---------------------------------------------------------------------- *)
(**
** Negative 5 (CONVERSION): the target category is the opposite one on
       its objects and its homs, but not as a whole record

--------
** 负 5（转换）：目标范畴在其对象和同态上是相反的，但整体记录则不是
*)

(*
The rejection is NOT at [id] or [compose]: both agree at [eq_refl], as
   does the hom-setoid's [equiv], and the four controls below say so --
   the first two are the target's own [galois_PG_obj] and [galois_PG_hom]
   restated.  What differs is the [homset] record, whose [Equivalence]
   witness is [Proset]'s opaque [Program] obligation applied at [(S, T)]
   on one side and [(T, S)] on the other, together with the rebuilt law
   fields; so the negative measures the record and not its data.

--------
拒绝不是发生在 [id] 或 [compose]：两者在 [eq_refl] 上是一致的，同样，hom-setoid 的 [equiv] 也是如此，并且下面四个控制也说明了这一点——前两个是目标自身的 [galois_PG_obj] 和 [galois_PG_hom] 的重述。不同的是 [homset] 记录，其 [Equivalence] 证人是 [Proset] 的不透明 [Program] 义务在一方的 [(S, T)] 上和另一方的 [(T, S)] 上应用，同时还有重建的法律字段；因此，否定的是记录本身，而不是其数据。
*)

Check (eq_refl : obj[Proset@{po Set} (stab_PreOrder_G Gp)]
                   = obj[(Subsets@{po Set} (grp_setoid Gp))^op]).

Check (fun S T : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)) =>
         (eq_refl : (S ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> T)
                      = (S ~{(Subsets@{po Set} (grp_setoid Gp))^op}~> T))).

Check (fun S : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)) =>
         (eq_refl : @id (Proset@{po Set} (stab_PreOrder_G Gp)) S
                      = @id ((Subsets@{po Set} (grp_setoid Gp))^op) S)).

Check (fun (S T U : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)))
           (f : T ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> U)
           (g : S ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> T) =>
         (eq_refl : @compose (Proset@{po Set} (stab_PreOrder_G Gp)) S T U f g
                      = @compose ((Subsets@{po Set} (grp_setoid Gp))^op)
                                 S T U f g)).

Fail Check (eq_refl : Proset@{po Set} (stab_PreOrder_G Gp)
                        = (Subsets@{po Set} (grp_setoid Gp))^op).

End AntitoneIsNotCovariant.

(* ------------------------------------------------------------------------ *)
(**
** Negatives 6 and 7 (FORMABILITY): [Subsets] identifies the two
       universes of the setoid it is handed

--------
** 负数6和7（可形成性）：[Subsets]识别它所接收的集合代数的两个宇宙
*)

(*
Instance/Powerset.v declares [Subsets (X : SetoidObject@{o o})], so
   forming the power set of a group's carrier IDENTIFIES that group's
   carrier and relation universes -- which is why the target's section
   binds [G : GrpObject@{gu o o}] with the level reused rather than
   [GrpObject@{gu o1 o2}].  (An earlier revision of this sentence wrote the
   instances as [@{o o gu}] and [@{o1 o2 gu}]; the roles permuted when
   [grp_prop] landed, and the reading is the same.)  [Subsets] is the LAST of four donors that
   each force it alone: [Powerset_Prop_obj] (Instance/Sets/Powerset.v,
   the one the target meets first), [subset_le] and [subset_le_preorder]
   are rejected at these very levels too (measured out of tree; only
   [Subsets] is pinned here).  The controls show that naming the group's
   setoid, and the group's homs, is fine at levels declared apart: what is
   rejected is the power set, and the same for the action.

--------
Instance/Powerset.v 声明了 [Subsets (X : SetoidObject@{o o})]，因此形成一个群的载体的幂集会识别该群的载体和关系的全集——这就是为什么目标部分将 [G : GrpObject@{gu o o}] 与重用的级别绑定而不是 [GrpObject@{gu o1 o2}]。（这句话的早期版本将实例写作 [@{o o gu}] 和 [@{o1 o2 gu}]；当 [grp_prop] 登场时，角色发生了置换，阅读结果相同。）[Subsets] 是四个强制其单独存在的捐赠者中的最后一个：[Powerset_Prop_obj]（Instance/Sets/Powerset.v，目标首先遇到的那个）、[subset_le] 和 [subset_le_preorder] 在这些级别上也被拒绝（在树之外测量；这里只有 [Subsets] 被固定）。控制显示，在声明不同的级别时命名群的集合等价类和群的同态是没有问题的：被拒绝的是幂集，动作也是同理。
*)

Section SubsetsIdentifies.

Universe qo qh qgu.
Constraint qo < qh.
Constraint qh <= qgu.

Context (Gq : GrpObject@{qgu qo qh}).
Context (Aq : MSetoidAction@{qo qh qgu qgu qgu qo qh qgu}
                (grp_mon@{qgu qo qh} Gq)).

(* Controls, at those very levels. / 在那些级别上进行控制。 *)
Check (grp_setoid Gq).
Check (act_setoid Aq).
Check (carrier (grp_setoid Gq)).
Check (grp_mon@{qgu qo qh} Gq).

Fail Check (Subsets (grp_setoid Gq)).

Fail Check (Subsets (act_setoid Aq)).

End SubsetsIdentifies.

(* ------------------------------------------------------------------------ *)
(**
** Formerly Negative 8 (FORMABILITY): Instance/Grp.v's [Z2] was pinned
    at [Set]

--------
** 以前为负8（可形成性）：实例/组.v 的 [Z2] 被固定在 [Set]
*)

(*
[Z2@{u} : GrpObject@{u Set Set}] -- its CARRIER and relation universes
   are both the literal [Set], not parameters -- so its carrier cannot be the
   source of a [Powerset_Prop_obj], whose own [Set < o] then cannot be met.
   (An earlier revision quoted [GrpObject@{u Set u}]; re-measured after the
   PR "algebraic carriers are sets" (2026-09-17), which permuted the record's
   universe roles and pinned the carrier as well.  The obstruction is if
   anything sharper and the conclusion is unchanged.)  That is
   why the target builds [GalZ2] over [eq_Setoid] instead.  The control
   shows the group itself, and its setoid, are perfectly nameable.

   CORRECTION (#450).  Everything above in this comment describes the
   tree before #450, which annotated [Z2] in place:
   [Z2@{p} : GrpObject@{p p p}], over [bool_setoid@{u} : Setoid@{u u}
   bool].  The negative below then stopped being refused (the build
   reported the guarded command accepted) and is kept, without the
   guard, as a control.  The target's [GalZ2] is left as it is.

--------
[Z2@{u} : GrpObject@{u Set Set}]——它的载体及相关宇宙
   都是字面上的 [Set]，而不是参数——所以它的载体不能是
   [Powerset_Prop_obj] 的来源，而 [Powerset_Prop_obj] 的 [Set < o] 随之无法满足。
   （早期的修订引用了 [GrpObject@{u Set u}]；在 PR “代数载体是集合”（2026-09-17）之后重新测量，该 PR 调换了记录的宇宙角色并固定了载体。阻碍是如果有什么更尖锐的结论也不变。）这就是为什么目标要在 [eq_Setoid] 上构建 [GalZ2] 的原因。控制显示群本身及其集合效应都是完全可以命名的。

更正（#450）。上面评论中描述的所有内容都是关于 #450 之前的树，它将 [Z2] 标注在原位：[Z2@{p} : GrpObject@{p p p}]，在 [bool_setoid@{u} : Setoid@{u u} bool] 上。下面的负面情况随后不再被拒绝（构建报告表示受保护的命令被接受）并被保留，作为控制，不包含保护。目标的 [GalZ2] 保持原样。
*)

Check @Z2.
Check (grp_setoid Z2).
Check (Subsets (grp_setoid GalZ2)).

Check (Subsets (grp_setoid Z2)).

(* ------------------------------------------------------------------------ *)
(** ** Positive: the two witnesses, and what they compute / ** 积极的：两个证人，以及他们所计算的 *)

Check (stab (A := GalZ2Act) galois_true).
Check (stab_Subgroup GalV4 GalV4Act galois_true).
Check (group_action_AdjointOnTheRight GalZ2 GalZ2Act).
Check (group_action_adjunction GalZ2 GalZ2Act).
Check (closed_G_iff GalZ2 GalZ2Act galois_true).
Check (closed_U_iff GalZ2 GalZ2Act galois_true).
Check (ClosedG GalZ2Act galois_true).
Check (ClosedU (A := GalZ2Act) galois_true).
Check (subset_le_antisym (X := galois_two)).
Check (gal_lrl_below (stab_PreOrder_U GalZ2 GalZ2Act)
         (group_action_galois GalZ2 GalZ2Act)).
Check (gal_lrl_above (stab_PreOrder_G GalZ2)
         (group_action_galois GalZ2 GalZ2Act)).
Check (gal_closed_l_iff (stab_PreOrder_U GalZ2 GalZ2Act)
         (stab_PreOrder_G GalZ2)
         (group_action_galois GalZ2 GalZ2Act)).
Check (StabOp GalZ2 GalZ2Act).
Check (FixedOp GalZ2 GalZ2Act).
Check galois_stab_true_trivial.
Check galois_v4_stab_proper.
