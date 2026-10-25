(**
* Probe for the necessity of the solution set condition (issue #444)

    Pins the two universe-instance boundaries that carry this development's
    headline, and nothing else.  Both are measured in the two targets'
    headers; measured is not guarded, which is what this file is for.

    THE BOUNDARY IS THAT ONE LIBRARY CLASS IS INHABITED AT ONE UNIVERSE
    INSTANCE AND REFUTED AT ANOTHER, over one and the same category.
    [Complete] at the SMALL instance (diagram shape strictly below the
    ambient objects) holds of the reversed order on the large ordinals;
    [Complete] at the COLLAPSED instance (shape at the object level) is
    refuted there.  N1-N3 pin the refused side and the [Check]s beside them
    pin the inhabited side, so neither can drift without this file stopping.

    N4 is the sharpest of the four: it feeds the INHABITED instance to the
    constant that REFUTES the collapsed one.  If that ever succeeded the
    development would prove False, so this refutation is the guard on the
    whole two-instances framing.

    N5 records that [Complete_Initial] is inert on the large categories --
    the measurement that redirected the issue -- against the accepted
    control on the thin one, which is Freyd's collapse appearing as a
    universe constraint.

    Each refutation was stripped ONE AT A TIME in a copy of this WHOLE file
    and its refusal read.  Only the STABLE HEAD of each refusal is described
    here, never the trailing clause, which is import-sensitive.

--------
* 探讨解集条件的必要性（问题 #444）

固定承载此开发标题的两个宇宙实例边界，仅此而已。 两者都在两个目标的头部进行测量；测量不是受保护的，这正是此文件的用途。

界限在于一个库类在一个宇宙实例中被占用，而在另一个实例中被驳回，都是在同一个类别上。小实例（图形严格低于环境对象）上的 [Complete] 适用于大序数上的逆序；折叠实例（对象级别的形状）上的 [Complete] 在那里被驳回。N1-N3 固定了被驳回的一方，而它们旁边的 [Check] 固定了被占用的一方，因此在没有此文件阻止的情况下，两者都无法漂移。

N4 是四个中最锋利的：它将被居住的实例喂给驳倒已崩溃实例的常量。如果那曾经成功过，开发就会被证明是假的，所以这种驳斥是整个双实例构架的防护。

N5 记录了 [Complete_Initial] 在大类别上是惰性的——这是重定向问题的测量——相对于薄类别上的已接受控制，即 Freyd 的塌缩表现为一个宇宙约束。

每条反驳在这个完整文件的副本中被一次一次剥离，并阅读其拒绝。这里只描述每条拒绝的稳定部分，绝不描述尾部从句，因为尾部从句依赖上下文。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Size.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Category.Adjunction.GAFT.Necessity.
Require Import Category.Instance.Ordinal.Large.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(* instrument: the refutation keyword is live in this file / 工具：反驳关键词在此文件中实时生效 *)
Fail Check probe444_absent_name.

(** ** The inhabited side, as positive controls / ** 有人居住的一侧，作为阳性对照 *)

Check SmallOrd_op_Complete.
Check SmallOrd_self_limit.
Check SmallOrd_no_greatest.
Check SmallOrd_op_not_large_complete.

(** ** N2-N3: [Complete] is refused wherever the collapsed instance is forced / ** N2-N3：无论何时强制折叠实例，[Complete] 都会被拒绝 *)

(*
An ascription alone does NOT pin the instance, and the first draft of this
   probe got that wrong: [Definition _ : @Complete SmallOrd_op_Proset :=
   SmallOrd_op_Complete.] is ACCEPTED, because Coq is free to instantiate the
   ascription's universes at the small instance.  So the collapsed instance
   has to be forced by a CONSUMER that demands it, which is what N2 and N4
   do.  That mistaken first draft is recorded rather than deleted, because
   "refuted by ascription" is the tempting wrong way to state this boundary.

   N2: [Complete_Initial] demands the collapsed instance, and the ordinals'
   small-instance witness does not meet it.

--------
仅仅一个类型标注并不能固定实例，而且这个探测的初稿搞错了：[Definition _ : @Complete SmallOrd_op_Proset := SmallOrd_op_Complete.] 被接受了，因为 Coq 可以在小实例上实例化类型标注的 universes。因此，折叠后的实例必须由一个要求它的使用者强制，这正是 N2 和 N4 所做的。之所以保留而不删除那个错误的初稿，是因为“被类型标注驳斥”是一个容易产生误导的错误表述这个边界的方法。

N2：[Complete_Initial] 需要折叠后的实例，而这些序数的小实例证据不符合要求。
*)
Fail Check (Complete_Initial SmallOrd_op_Complete).

(*
N3: the same for the tree's large witnesses, which is what makes N5's
   control the only accepted one.

--------
N3：对于树的大见证者也是一样，这就是使N5的控制成为唯一被接受的原因。
*)
Fail Check (Complete_Initial Sets_Complete).
Fail Check (Complete_Initial Grp_Complete).
Fail Check (Complete_Initial Ab_Complete).

(**
** N4: the two instances cannot be fed to each other

    This is the guard on the whole framing.  [SmallOrd_op_not_large_complete]
    takes the COLLAPSED instance and returns [False]; [SmallOrd_op_Complete]
    inhabits the SMALL one.  If the application below ever went through, the
    development would prove [False].

--------
** N4：这两个实例不能互相输入

这是整个框架的保护。[SmallOrd_op_not_large_complete] 接受 COLLAPSED 实例并返回 [False]；[SmallOrd_op_Complete] 位于 SMALL 实例中。如果下面的应用程序曾经执行过，开发将会证明 [False]。
*)

Fail Definition p444_boom : False :=
  SmallOrd_op_not_large_complete SmallOrd_op_Complete.

(** ** N5: the accepted control — Freyd's collapse, and only it / ** N5：被接受的控制——弗雷德的崩溃，唯独它 *)

Section ThinWitness.
Context (X : SetoidObject).
(*
ACCEPTED: the thin powerset lattice is large-complete, and is the one
   witness in tree that is.

--------
已接受：薄幂集格是大完备的，并且是树中唯一一个这样的证明。
*)
Check (Complete_Initial (Subsets_Complete (X:=X))).
End ThinWitness.

(** ** Guard block / ** 防守格挡 *)

Check @ConstOne.
Check @ConstOne_continuous.
Check @ConstOne_representable_iff_initial.
Check @ConstOne_not_representable.
Check @Complete_Initial.
(*
NOTE: [Initial] is a NOTATION (Structure/Initial.v), so writing
   [Check @Initial_of_limit_id.] makes the parser read the notation applied
   to [_of_limit_id] and report that reference as absent.  The qualified
   name sidesteps it.

--------
注意：[Initial] 是一个符号表示（Structure/Initial.v），所以写 [Check @Initial_of_limit_id.] 会使解析器读取应用于 [_of_limit_id] 的符号表示并报告该引用缺失。限定名称可以绕过它。
*)
Check Category.Adjunction.GAFT.Necessity.Initial_of_limit_id.
Check @SmallShapeComplete.
Check @SmallOrd.
Check @ole.
Check @ojoin.
Check @SmallOrd_op_Proset.
Check @Subsets_Complete.
