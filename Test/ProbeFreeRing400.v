Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(**
* Boundary probe for issue #400 (maclane:IV.8:ex2)

    Instance/Ab/Free.v, Instance/Mon/Free.v and Instance/Rng/Free.v each
    carry their own [Fail] probes.  Those guard their measurements from
    INSIDE, which is exactly what a whole-file rename cannot test: rename
    a definition and its in-file [Fail] renames with it, so the guard goes
    vacuously green.  This file restates the three cross-file boundaries
    from OUTSIDE, each against a positive control that NAMES the same
    constants, so that renaming any of them breaks this file loudly.

    Negatives are grouped BY KIND and the groups are kept lexically
    apart.  Each was stripped of its [Fail] once and the resulting error
    read, and the kind recorded here is the kind that actually fired.

--------
* 边界探测器用于问题 #400 (maclane:IV.8:ex2)

Instance/Ab/Free.v、Instance/Mon/Free.v 和 Instance/Rng/Free.v 各自
携带它们自己的 [Fail] 探测器。这些探测器从内部保护它们的测量，而这正是整个文件重命名无法测试的：重命名一个定义及其文件中的 [Fail]，一起重命名，这样保护器就显然是绿色的。该文件从外部重新声明了三个跨文件边界，每个边界都针对一个正控制，该控制命名了相同的常量，因此重命名其中任何一个都会显著破坏此文件。

负面案例按类型分组，并保持组之间的词法间隔。每个负面案例曾被移除一次 [Fail]，并记录生成的错误类型，此处记录的类型是实际触发的类型。
*)

(**
** Positive controls

    Every constant named in a negative below is also named here, outside
    any [Fail], so a rename cannot silently vacate a guard.

--------
** 阳性对照

    下面负面中提到的每一个常量在这里也都有命名，且在任何 [Fail] 之外，因此重命名不会悄无声息地使保护失效。
*)

Check @free_ring_via_ab.
Check @free_ring_via_mon.
Check @free_ring_composites_agree.
Check @RngUnderlyingAb.
Check @RngUnderlyingMon.
Check @free_ring_via_mon_adjunction.
Check @free_ring_via_mon_adjunction_ab.
Check @FreeAb.
Check @free_ab_adjunction.
Check @FreeMonSets.
Check @free_mon_sets_adjunction.
Check @FreeRngAb.
Check @free_rng_ab_adjunction.
Check @MonoidRingFunctor.
Check @zmring_adjunction.
Check @Rng_Forget_Ab.
Check @Rng_Forget_Mon.
Check @Rig_Forget_Mon.
Check (Rng_Forget_Mon : Rng ⟶ MonSets).

(**
** Positive controls: what DOES hold strictly

    The two underlying-set functors of the two routes agree on objects
    and on arrows definitionally.  These are the facts that make the
    field-copying retype below possible, so they are controls for the
    conversion negatives that follow.

--------
** 阳性对照：严格成立的内容

    两条路径的两个基础集合函子在对象和箭头上定义上是一致的。这些事实使得下面的字段复制重新类型化成为可能，因此它们是随后的转换负面结果的对照。
*)

Example probe_fobj_agree (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R := eq_refl.

Example probe_fmap_agree (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f := eq_refl.

(**
** CONVERSION negatives

    Agreement on [fobj] and [fmap] does NOT extend to the functor
    records, nor to the [Adjunction] record built over them.

--------
** 转换负面情况

    对 [fobj] 和 [fmap] 的协议 **不** 扩展到函子记录，也不扩展到建立在其上的 [Adjunction] 记录。
*)

(*
The two right adjoints are not the same record: the law fields are
   [Compose]'s obligations at different arguments.

--------
这两个右伴随不是相同的记录：法律字段是在不同参数下 [Compose] 的义务。
*)
Fail Example probe_underlying_records_agree :
  RngUnderlyingAb = RngUnderlyingMon := eq_refl.

(*
And the monoid route's adjunction cannot simply be ASCRIBED against
   the abelian route's right adjoint, even though every field type is
   convertible: the [Adjunction] type mentions the right adjoint as a
   whole record.  This is precisely why Instance/Rng/Free.v rebuilds it
   field by field as [free_ring_via_mon_adjunction_ab] rather than
   transporting along a natural isomorphism.

--------
并且单子路径的伴随不能简单地归因于阿贝尔路径的右伴随，尽管每种域类型都是可转换的：[Adjunction] 类型以整体记录的形式提到了右伴随。这正是 Instance/Rng/Free.v 按字段重建为 [free_ring_via_mon_adjunction_ab] 的原因，而不是沿自然同构进行传输。
*)
Fail Definition probe_ascribe_mon_at_ab
  : free_ring_via_mon ⊣ RngUnderlyingAb
  := free_ring_via_mon_adjunction.

(**
** FORMABILITY negative

    A different KIND: not a failed conversion but a universe
    inconsistency.  The monoid route is confined to rings whose homs live
    in [Set], because [Rig_Forget_Mon]'s source is [Rig@{u Set}]; the
    abelian route is not.  What the negative fires on is the donor's
    literal [Set] meeting the RIGID declared level [puh]: unification
    cannot set a rigid level to [Set], and deleting the [Constraint]
    below leaves the negative failing with the identical message
    ("Cannot enforce Set = puh"), so the [Constraint] is INERT for the
    negative and it would be wrong to say the negative fires on it.  Its
    real work is on the POSITIVE control, which without it would not say
    "elaborates strictly above [Set]".  The control rules out the
    ascription shape, which is all a control can rule out.

--------
** FORMABILITY 否定

    另一种类型：不是转换失败，而是宇宙不一致。幺半群路径仅限于其同态存在于 [Set] 的环，因为 [Rig_Forget_Mon] 的源是 [Rig@{u Set}]；阿贝尔路径则不受此限。否定触发的对象是施主的字面 [Set] 与 RIGID 声明级别 [puh]：统一不能将刚性级别设为 [Set]，而删除下方的 [Constraint] 会使否定仍以相同的消息失败（“无法强制 Set = puh”），因此 [Constraint] 对否定来说是惰性的，说否定触发它是不对的。它真正起作用的是 POSITIVE 控制，没有它就不会显示“严格展开于 [Set] 之上”。该控制排除了赋值形态，而控制所能排除的也仅限于此。
*)

Section ProbeMonRouteSetPin.

Universe puo puh.
Constraint Set < puh.

Check (Rng_Forget_Ab : Rng@{puo puh} ⟶ Ab).

Fail Check (Rng_Forget_Mon : Rng@{puo puh} ⟶ MonSets).

End ProbeMonRouteSetPin.

(**
** Instrument check

    A [Fail] that must fail for a reason having nothing to do with #400,
    so that a broken [Fail] mechanism would be visible here rather than
    silently passing every negative above.

--------
** 仪器检查

    一个 [Fail] 必须因为与 #400 无关的原因而失败，
    这样在这里就可以看到损坏的 [Fail] 机制，而不是
    默默地通过上面的每个否定项。
*)

Fail Example probe_free_ring_instrument : (true = false) := eq_refl.
