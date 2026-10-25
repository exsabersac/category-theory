(**
* Probe for Instance/Ab/FreeNotContinuous.v (issue #430)

    Pins the measured boundaries of the discontinuity witness with
    negatives of three kinds, kept lexically apart: CONVERSION (N1-N3: the
    identifications the proofs use — the image of the point's terminal
    arrow is [id], the image legs are [id], the free group on a point is
    not the zero group — hold at [≈] or as theorems, never on the nose);
    TYPING (N4-N5: the cone-level refutations do not ascribe at the
    apex-only classes — [ContinuousFunctor] against [PreservesAllLimits],
    and the binary witness against [PreservesLimit] — so the header's
    "only the empty shape reaches the apex level" is a measured boundary);
    UNIVERSE (N6-N8: [Ab_trivial], [Ab_Terminal] and [Ab_Cartesian] are
    refused at a hom level strictly above [Set] while [Ab] and [Ab_Forget]
    are accepted there — the [Set] pin is the trivial group's, Instance/
    Ab.v, not the category's).  Three [eq_refl] readbacks (the carrier
    of the free group on a point, the binary diagram's objects, the zero
    endomorphism's value) are positive controls, the last making
    [ab_zero_endo]'s [Defined] load-bearing.  Each refutation was stripped
    one at a time in a copy of the whole file; the import list mirrors the
    target's.  Section D's checks and the guard block are positive
    controls.

--------
* 探测实例/Ab/FreeNotContinuous.v（问题 #430）

用三类反例固定不连续性见证的测量边界，并在词汇上保持分离：

转换（N1-N3：证明所使用的识别——点的终端箭头的映像是 [id]，映像腿是 [id]，点上的自由群不是零群——在 [≈] 成立或作为定理成立，绝不完全相同）；

类型（N4-N5：锥级反证不在顶点唯一类上归属——[ContinuousFunctor] 对抗 [PreservesAllLimits]，以及二元见证对抗 [PreservesLimit]——因此标题“只有空形达到顶点级”是一个测量边界）；

宇宙（N6-N8：[Ab_trivial]、[Ab_Terminal] 和 [Ab_Cartesian] 在严格高于 [Set] 的同构层次上被拒绝，而 [Ab] 和 [Ab_Forget] 在那里被接受——[Set] 的固定针是平凡群的，Instance/Ab.v，而不是范畴的）。
三个 [eq_refl] 读取回读（点上的自由群的承载体，二元图的对象，零自同态的值）是阳性对照，最后一个使 [ab_zero_endo] 的 [Defined] 承重。每个驳斥在整个文件的副本中一次一个地剥离；导入列表与目标文件相对应。D 节的检查和守卫块是阳性对照。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Free.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Ab.FreeNotContinuous.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe430_absent_name.

(**
** A: CONVERSION — the identifications the proofs use hold at [≈], not
       on the nose

--------
** A: 转换 — 证明使用的识别在 [≈] 上成立，而不是完全成立
*)

(* controls: the [≈] forms are the file's own lemmas / 控制：[≈] 形式是文件自身的词条 *)
Check fmap_one_point.
Check free_ab_one_id_not_zero.

(*
N1 CONVERSION: the image of the point's terminal arrow is [id] up to [≈]
   ([fmap_one_point]), not definitionally

--------
N1 转换：点的终端箭头的图像是 [id] 到 [≈]（[fmap_one_point]），不是定义上的
*)
Fail Example p430_fmap_one_not_definitional :
  fmap[FreeAb] (@one Sets Sets_Terminal SetsPoint) = @id Ab (FreeAb SetsPoint)
  := eq_refl.

(* N2 CONVERSION: the image cone's legs, likewise / N2 转换：图像圆锥的腿，亦然 *)
Fail Example p430_image_leg_not_definitional :
  cone_leg (FCone FreeAb NatOneCone) 0%nat = @id Ab (FreeAb SetsPoint)
  := eq_refl.

(*
N3 CONVERSION: the free group on a point is not the zero group — nor is
   it convertible to it; the separation is a theorem, not a computation

--------
N3 转换：一个点上的自由群不是零群——它也不能转换为零群；这种分离是一个定理，而不是计算结果
*)
Fail Example p430_free_on_point_is_not_the_zero_group :
  FreeAb SetsPoint = Ab_trivial := eq_refl.

(** ** B: TYPING — the two strength levels do not ascribe into each other / ** B: 打字 — 两个强度级别不能互相转化 *)

(* controls: each refutation at its own level / 控制：每个反驳在其自身层面上 *)
Check (FreeAb_not_continuous : ContinuousFunctor FreeAb → False).
Check (FreeAb_not_PreservesAllLimits : PreservesAllLimits FreeAb → False).
Check (FreeAb_not_PreservesLimitCone_binary_product
         : PreservesLimitCone BinDiagram FreeAb → False).

(*
N4 TYPING: the cone-level conclusion is not the apex-level one — the
   latter needs the empty shape's separate argument

--------
N4 打字：圆锥层的结论不是顶点层的结论——后者需要空形状的单独论证
*)
Fail Definition p430_cone_level_is_not_apex_level :
  PreservesAllLimits FreeAb → False := FreeAb_not_continuous.

(* N5 TYPING: the binary witness reaches the cone level only / N5 打字：二进制证据仅达到圆锥水平 *)
Fail Definition p430_binary_witness_is_cone_level_only :
  PreservesLimit BinDiagram FreeAb → False
  := FreeAb_not_PreservesLimitCone_binary_product.

(** ** C: UNIVERSE — the [Set] pin is [Ab_trivial]'s, not [Ab]'s / ** C: 宇宙 — [Set] 引脚属于 [Ab_trivial]，而不是 [Ab] *)

Monomorphic Universe uo uh.
Monomorphic Constraint Set < uh.
Monomorphic Constraint uh < uo.

(*
controls: the category and its forgetful functor form at a hom level
   strictly above [Set]

--------
控制：该范畴及其遗忘函子在 hom 水平上严格高于 [Set]
*)
Check (Ab@{uo uh} : Category@{uo uh uh}).
(*
Three universes, not two: since the PR "algebraic carriers are sets"
   (2026-09-17) [Ab]'s object universe is bounded below by [Set] (the sort of
   [Prop], entering through [cmon_prop]), and [Sets]'s own object level is no
   longer identified with [Ab]'s.  The middle argument is that level; the
   roles of [uo] and [uh] are unchanged.

--------
三个宇宙，而不是两个：由于 PR “代数载体是集合”（2026-09-17）[Ab] 的对象宇宙由 [Set] 在下方界定（[Prop] 的范畴，通过 [cmon_prop] 进入），并且 [Sets] 自己的对象层不再与 [Ab] 认同。中间的论点是那个层次；[uo] 和 [uh] 的角色没有改变。
*)
Check (Ab_Forget@{uo uo uh}).

(*
N6-N8 UNIVERSE: everything assembled from the trivial group is pinned
   at [Set]

--------
N6-N8 宇宙：由平凡群组装的一切都固定在 [Set]
*)
Fail Check (Ab_trivial : AbObject@{uh uh uh}).
Fail Check (Ab_Terminal : @Terminal Ab@{uo uh}).
Fail Check (Ab_Cartesian : @Cartesian Ab@{uo uh}).

(** ** D: readbacks / ** D：复读 *)

Example p430_freeab_is_left_adjoint : FreeAb ⊣ Ab_Forget := free_ab_adjunction.

Example p430_free_ab_one_carrier :
  carrier (Ab_Forget (FreeAb SetsPoint)) = FATerm SetsPoint := eq_refl.

Example p430_bin_diagram_objects : BinOnes true = SetsPoint := eq_refl.

Example p430_zero_endo_value (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (ab_zero_endo A) a = cmon_zero A := eq_refl.

Check FreeAb_not_PreservesLimit_empty.
Check FreeAb_not_PreservesLimitCone_empty.
Check FreeAb_not_PreservesLimitCone_countable_product.
Check FreeAb_binary_comparison_not_iso.
Check FreeAb_not_CartesianFunctor.
Check FreeAb_not_continuous_via_empty.
Check Ab_Forget_Continuous.
Check FreeAb_Cocontinuous.

(** ** Guard block / ** 防守格挡 *)

Check @FreeAb.
Check @SetsPoint.
Check @NatOneCone.
Check @BinDiagram.
Check @Ab_trivial.
Check @Ab_Terminal.
Check @Ab_Cartesian.
Check @Ab.
Check @Ab_Forget.
Check @AbObject.
Check @ab_zero_endo.
Check @FreeAb_not_continuous.
Check @FreeAb_not_PreservesLimitCone_binary_product.
Check @PreservesAllLimits.
Check @PreservesLimit.
Check @PreservesLimitCone.
Check @ContinuousFunctor.
Check @cone_leg.
Check @FCone.
Check @fmap.
Check @one.
Check @id.
Check @Terminal.
Check @Cartesian.
Check @Category.
Check @Sets_Terminal.
Check nat.
