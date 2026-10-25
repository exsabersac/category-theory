(**
* Boundary probe for the orthogonal-complement connection (#385)

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

    Six negatives plus one instrument check.  The kinds are told apart by
    the error TEXT rather than by a label, and every one was stripped ONE
    AT A TIME, compiled alone, and its whole message read.

      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and NO universe
                   clause.  Negatives 2, 3 and 4.

      CONVERSION   "cannot unify" between two inhabitants of ONE type.
                   Negatives 5 and 6.

      FORMABILITY  ends in "universe inconsistency: Cannot enforce ...".
                   Negative 7.

    Every constant a negative names also appears in a command OUTSIDE any
    [Fail], donors included -- a guard that names a constant only inside
    its own [Fail] is vacuous, and the control block below was written by
    reading the [Fail] commands rather than from memory.

--------
* 用于正交补连接的边界探针 (#385)

这个文件的存在是为了处理文件内部的 [Fail] 做不到的事情：在重命名时仍然存在。在它所保护的模块中写入的负值会随着它所命名的常量同步重命名，因此当该常量消失时仍保持绿色；而在这里写入的负值会大声报错。

下面的 [Require] 列表是目标本身的列表，加上目标本身。一个简短的前缀恰恰会让探针因错误的原因通过——缺失的强制或符号注释可能会将预期的统一不匹配变为“非法应用”——因此该列表是镜像的，而不是裁剪的。

** 负面因素，按种类

六个负片加一个仪器检查。这些种类是通过错误文本而不是标签来区分的，每个负片都是一次剥离，一个接一个地单独编译，并读取其整个信息。

输入一个简单的“具有类型...，而预期具有类型...”，没有“无法统一”和没有宇宙子句。否定项 2、3 和 4。

转换 “不能统一” 在同一类型的两个实例之间。负数 5 和 6。

FORMABILITY  以“universe inconsistency: Cannot enforce ...”结束。负 7。

每个常量一个负名称也出现在任何 [Fail] 之外的命令中，包括捐赠者——一个仅在其自己的 [Fail] 内命名常量的保护是无效的，下面的控制块是通过读取 [Fail] 命令而不是从内存中编写的。
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
Require Import Category.Instance.Grp.Galois.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.InnerProduct.Galois.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

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
Fail Check probe385_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(** ** Controls for the constants the negatives name / ** 控制常数否定的名称 *)

Check @subset_le.
Check @subset_le_preorder.
Check @subset_le_antisym.
Check @Subsets.
Check @op_rel.
Check @op_PreOrder.
Check @Proset.
Check @GaloisConnection.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_truth.
Check @AdjointOnTheRight.
Check @AdjointOnTheLeft.
Check @PerpRel.
Check @Build_PerpRel.
Check @perp.
Check @perp_sym.
Check @perp_respects.
Check @perp_respects_iff.
Check @perp_set.
Check @perp_set_mem.
Check @perp_transpose.
Check @perp_set_antitone.
Check @perp_set_respects.
Check @perp_galois.
Check @perp_galois_l_is_r.
Check @perp_to_is_from_swapped.
Check @perp_PreOrder_l.
Check @perp_PreOrder_r.
Check @perp_unit.
Check @perp_counit.
Check @perp_unit_is_counit.
Check @perp_triple.
Check @ClosedPerp.
Check @perp_set_closed.
Check @closed_perp_iff.
Check @PerpFunctor.
Check @PerpFunctor_r.
Check @perp_adjunction.
Check @PerpOp.
Check @perp_AdjointOnTheRight.
Check @perp_aor_to.
Check @perp_aor_from.
Check @zz_setoid.
Check @zdot.
Check @ZZPerp.
Check @zz_sub.
Check @zz_e1.
Check @zz_yaxis.
Check @zz_xaxis.
Check @zz_perp_is_dot.
Check @zz_perp_e1_is_yaxis.
Check @zz_perp_yaxis_is_xaxis.
Check @zz_e1_not_ClosedPerp.
Check @zz_yaxis_ClosedPerp.
Check @zz_e1_not_self_perp.
Check @zz_axes_differ.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 2-6, at an abstract setoid / ** 在抽象集合上取负 2-6 *)

Section AbstractBoundary.

Universe po pu.
Constraint Set < po.

Context (Xp : SetoidObject@{po po}).
Context (Pp : PerpRel@{po} Xp).

(* ---------------------------------------------------------------------- *)
(** ** Negative 2 (TYPING): the connection is antitone, not covariant / ** 负2（打字）：连接是反变的，而不是协变的 *)

(*
Mac Lane types the two maps as [L : P → Q^op] and [R : Q^op → P]:
   taking complements REVERSES inclusion, so the covariant record of #380
   is inhabited only once the second relation is reversed.  The control
   shows the antitone reading is the one that holds.

--------
Mac Lane 将这两个映射类型定义为 [L : P → Q^op] 和 [R : Q^op → P]：取补集会反转包含关系，所以 #380 的协变记录只有在第二个关系被反转后才有元素。控制显示反单调读取才是成立的。
*)

Check (perp_galois Pp
        : GaloisConnection (@subset_le@{po} Xp)
            (op_rel (@subset_le@{po} Xp))).

Fail Check (perp_galois Pp
             : GaloisConnection (@subset_le@{po} Xp)
                 (@subset_le@{po} Xp)).

(* ---------------------------------------------------------------------- *)
(** ** Negative 3 (TYPING): right-adjointness is not left-adjointness / ** 负 3（打字）：右伴随性不是左伴随性 *)

(*
Adjunction/Right.v's [right_does_not_imply_left] shows the two
   classes come apart in general.  Here the point is narrower and is a
   fact about TYPES only: the record built for one slot is not a term of
   the other slot's type.  Nothing below claims that [PerpOp] is not
   adjoint on the left; that is neither proved nor refuted anywhere.

--------
Adjunction/Right.v 的 [right_does_not_imply_left] 显示了这两个类通常是分开的。这里的重点更狭窄，仅仅是一个关于类型的事实：为一个插槽构建的记录不是另一个插槽类型的项。下面没有任何内容声称 [PerpOp] 在左侧不是伴随；这在任何地方都没有被证明或反驳。
*)

Check (perp_AdjointOnTheRight Pp
        : AdjointOnTheRight (PerpOp Pp) (PerpOp Pp)).

Fail Check (perp_AdjointOnTheRight Pp
             : AdjointOnTheLeft (PerpOp Pp) (PerpOp Pp)).

(* ---------------------------------------------------------------------- *)
(** ** Negative 4 (TYPING): [L = R] is about the MAPS, not the functors / ** 负4（打字）：[L = R] 是关于地图的，而不是函子 *)

(*
[perp_galois_l_is_r] closes by [eq_refl], so Mac Lane's [L S = R S]
   holds on the nose at the level of the two fields.  It does NOT lift to
   the two functors those fields induce: [PerpFunctor] runs from
   [Subsets X] to the reversed order and [PerpFunctor_r] the other way, so
   the two do not share a type at all and the equation between them
   cannot even be stated.  Both functors are named in the controls.

--------
[perp_galois_l_is_r] 由 [eq_refl] 封闭，因此 Mac Lane 的 [L S = R S] 在两个域的层面上正好成立。它不会提升到那些域所引出的两个函子：[PerpFunctor] 从 [Subsets X] 运行到逆序，而 [PerpFunctor_r] 方向相反，因此这两个函子根本没有共享类型，它们之间的等式甚至无法陈述。两个函子都在控件中被命名。
*)

Check (PerpFunctor Pp
        : Subsets@{po pu} Xp ⟶ Proset@{po pu} (@perp_PreOrder_r Xp)).
Check (PerpFunctor_r Pp
        : Proset@{po pu} (@perp_PreOrder_r Xp) ⟶ Subsets@{po pu} Xp).
Check (perp_galois_l_is_r Pp).

Fail Check (PerpFunctor Pp = PerpFunctor_r Pp).

(* ---------------------------------------------------------------------- *)
(** ** Negative 5 (CONVERSION): the triple complement collapses at [≈] / ** 负 5（转换）：三重补码在 [≈] 崩溃 *)

(*
[perp_triple] is an equation between OBJECTS of the power set, held at
   the carriers' own [≈]; the two sides are different terms and no
   unfolding identifies a triple composite with a single one.

--------
[perp_triple] 是幂集对象之间的一个等式，保存在承载者自己的 [≈] 上；两边是不同的项，没有任何展开会将三重组合识别为单个。
*)

Check (fun S => perp_triple Pp S
         : perp_set Pp (perp_set Pp (perp_set Pp S)) ≈ perp_set Pp S).

Fail Check (fun S : carrier (Powerset_Prop_obj@{po} Xp) =>
              (eq_refl : perp_set Pp (perp_set Pp (perp_set Pp S))
                           = perp_set Pp S)).

End AbstractBoundary.

(* ------------------------------------------------------------------------ *)
(** ** Negative 6 (CONVERSION): the witness identifications are at [≈] / ** 负 6（转换）：证人身份认定在 [≈] *)

(*
Over ℤ² the complement of the singleton [{(1,0)}] and the second axis
   are the same SUBSET, but they are built as two different
   [SetoidMorphism] records -- one a quantified condition over a
   singleton, the other a bare coordinate equation -- so the
   identification holds at [≈] and not on the nose.

--------
在 ℤ² 上，单点集 [{(1,0)}] 的补集和第二条坐标轴是相同的子集，但它们是作为两个不同的 [SetoidMorphism] 记录构建的——一个是对单点的量化条件，另一个是一个简单的坐标方程——因此这个等同在 [≈] 上成立，而不是直接成立。
*)

Check (zz_perp_e1_is_yaxis : perp_set ZZPerp zz_e1 ≈ zz_yaxis).

Fail Check (eq_refl : perp_set ZZPerp zz_e1 = zz_yaxis).

(* ------------------------------------------------------------------------ *)
(** ** Negative 7 (FORMABILITY): the carrier and relation levels coincide / ** 负7（可形成性）：载体水平和关系水平一致 *)

(*
[PerpRel@{o}] is declared over [SetoidObject@{o o}], so it does not
   accept a setoid whose two levels are declared apart.  Read that at its
   true strength: the rejection lands on the ARGUMENT, and [PerpRel]
   cannot be tested apart from it, its parameter type BEING
   [SetoidObject@{o o}].  Read that precisely: the record's three fields
   do NOT force the identification -- the same three fields declared over
   [SetoidObject@{o1 o2}] are accepted and apply at levels declared apart
   (measured out of tree by an audit, not pinned here) -- so the [@{o}]
   binder is a declaration CHOICE aligning the record with
   [Powerset_Prop_obj], and it is that donor, whose rejection is pinned as
   negative 6 of Test/ProbeQuantifier384.v and cited rather than repeated,
   that makes the choice unavoidable downstream.  An earlier draft said
   this negative measured an inherited shape rather than a demand of the
   record's own, which overstated what it measures.  The
   controls show the setoid, its carrier and its structure are all fine at
   these levels.

--------
[PerpRel@{o}] 在 [SetoidObject@{o o}] 之上声明，因此它不接受两个层次被分开声明的集合。正确理解这一点：拒绝作用于参数，而 [PerpRel] 无法在没有参数的情况下进行测试，其参数类型为 [SetoidObject@{o o}]。仔细阅读：记录的三个字段并不强制识别 —— 在 [SetoidObject@{o1 o2}] 上声明的相同三个字段被接受，并且适用于单独声明的级别（由审计从树中测量，而不是固定在此处） —— 因此 [@{o}] 绑定器是一个声明选择，使记录与 [Powerset_Prop_obj] 对齐，而正是那个捐赠者，其拒绝被固定为 Test/ProbeQuantifier384.v 的负 6 并被引用而非重复，下游就不可避免地必须做出该选择。早期的草稿说，这个负面衡量的是继承的形状，而不是唱片自身的需求，这夸大了它所衡量的内容。控制数据显示，这些层次上的集合、其承载体及其结构都是好的。
*)

Section UniverseBoundary.

Universe qo qh.
Constraint qh < qo.

Context (Aq : SetoidObject@{qo qh}).

Check (carrier Aq).
Check (is_setoid Aq).
Check (Aq : Type@{qo}).

Fail Check (PerpRel Aq).

End UniverseBoundary.
