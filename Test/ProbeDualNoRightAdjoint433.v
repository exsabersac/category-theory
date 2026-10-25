(**
* Probe for Instance/FdVect/NoRightAdjoint.v and Instance/Mod/Product.v
      (issue #433)

    Pins the measured boundaries of the conditional refutation with
    negatives of two kinds, kept lexically apart (an earlier revision said
    three; the correction is below): CONVERSION (N1: the
    tree has TWO dual functors on [Vct_F F] — Instance/FdVect/DoubleDual.v's
    [Dual F], precomposition on the nose, and Structure/Monoidal/
    StarAutonomous.v's [dual] read at the line through Instance/Mod/
    Closed.v's [RMod_SymMonClosed], the target's [VctDual359]; they are
    naturally isomorphic ([dual_iso359]) but built by different [Program]
    records and NOT convertible; N5: not even objectwise — the packed
    modules [VctDual359 F x] and [Dual F x] are refused at [eq_refl] while
    their carriers are accepted, the control beside it); TYPING (N2: the
    refutation is CONDITIONAL — the unconditional statement [∀ Rt, Dual F ⊣
    Rt → False] does not ascribe, [CoordSpanProper F] being the premise;
    N3: the self-adjunction runs [(Dual F)^op ⊣ Dual F], and the exercise's
    direction [Dual F ⊣ (Dual F)^op] is exactly the ascription that is
    refused).  RECORDED CORRECTION: an earlier revision listed a fourth
    kind, UNIVERSE, for N4 — "Instance/Discrete.v's unannotated
    [DiscreteCat_Functor] pins the shape's hom level to [Set], so no cocone
    over it lives in [Vct^op] — the reason the diagram uses
    Structure/Limit/Comparison.v's [DiscreteCat_Functor']".  The donor was
    annotated in place in the PR "algebraic carriers are sets"
    (2026-09-17), Instance/Discrete.v, and the cocone type IS now
    formable; §C keeps the line as a positive control and no UNIVERSE
    refusal remains here.  The [eq_refl]
    readbacks are positive controls (the coordinate projections, the
    transpose, the colimit mediator and the isomorphism's components
    compute), and the #359 control shows Structure/Monoidal/Dual.v's
    self-adjunction instantiates at [VctDual359].  Each refutation was
    stripped one at a time in a copy of the whole file; the import list
    mirrors the target's, plus Structure/Monoidal/Dual.v for that control
    and Structure/Limit/Product.v for the indexed-product readback.

--------
* 探查 Instance/FdVect/NoRightAdjoint.v 和 Instance/Mod/Product.v（问题 #433）

将条件反驳的测量边界固定为
 两种否定词，在词汇上保持分离（较早的修订版说
 三； 更正如下）： CONVERSION（N1：
 树在 [Vct_F F] 上有两个对偶函子 — Instance/FdVect/DoubleDual.v's
 [Dual F]，鼻子上的预合成，以及结构/Monoidal/
 StarAutonomous.v的[dual]通过Instance/Mod/在线读取
 Closed.v的[RMod_SymMonClosed]，目标的[VctDual359]； 他们是
 自然同构（[dual_iso359]）但由不同的 [Program] 构建
 记录且不可兑换； N5：甚至不是客观的——拥挤的
 模块 [VctDual359 F x] 和 [Dual F x] 在 [eq_refl] 上被拒绝，而
 他们的运营商被接受，控制在旁边）； 打字（N2：
 反驳是有条件的 — 无条件陈述 [∀ Rt, Dual F ⊣
 Rt→False]不归属，[CoordSpanProper F]为前提；
 N3：自我辅助运行 [(Dual F)^op ⊣ Dual F]，练习的
 [Dual F ⊣ (Dual F)^op] 方向正是以下的归属
 拒绝）。记录更正：之前的修订列出了第四种类型，UNIVERSE，用于 N4 —— “Instance/Discrete.v 中未注释的 [DiscreteCat_Functor] 将形状的同伦级固定到 [Set]，因此在 [Vct^op] 中不存在其余的 cocone —— 这也是该图使用 Structure/Limit/Comparison.v 的 [DiscreteCat_Functor'] 的原因”。在 PR “代数载体是集合”（2026-09-17）、Instance/Discrete.v 中，捐赠者已就地注释，并且 cocone 类型现在可以形成；§C 保留该行作为阳性对照，这里不再存在 UNIVERSE 拒绝。[eq_refl] 的回读是阳性对照（坐标投影、转置、余极中介和同构组件的计算），而 #359 控制显示 Structure/Monoidal/Dual.v 的自伴随在 [VctDual359] 处实例化。每个反驳都在整个文件的副本中一次移除一个；导入列表与目标文件相同，外加该控制的 Structure/Monoidal/Dual.v 和索引积回读的 Structure/Limit/Product.v。
*)

Require Import Coq.Lists.List.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Adjunction.Continuity.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Closed.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.FdVect.DoubleDual.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Monoidal.Dual.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.FdVect.NoRightAdjoint.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe433_absent_name.

Section Probe.

Context (F : FieldObject).

Notation Vct := (Vct_F F).

(**
** A: CONVERSION — two dual functors, naturally isomorphic, not
       convertible

--------
** A: 转换——两个对偶函子，自然同构，但不可转换
*)

(*
control: #359's headline, Structure/Monoidal/Dual.v's self-adjunction
   on the right, instantiates at the target's reading of [dual]

--------
控制：#359 的标题，Structure/Monoidal/Dual.v 的自伴随在右侧，在目标对 [dual] 的读取处实例化
*)
Definition p433_dual359_self_right :
  @AdjointOnTheRight Vct Vct (VctDual359 F) (VctDual359 F) :=
  @dual_self_adjoint_on_the_right Vct (VctSMC F) (VctLine F).

(*
control: the isomorphism is delivered, and the exercise holds for the
   functor the issue names

--------
控制：同构已传递，并且该练习适用于该函子所命名的问题
*)
Check (dual_iso359 F : Dual F ≈ VctDual359 F).
Check (dual359_no_right_adjoint F
         : CoordSpanProper F → ∀ Rt : Vct ⟶ Vct^op, VctDual359 F ⊣ Rt → False).

(* N1 CONVERSION: the two functors are different [Program] records / N1转换：这两个函子是不同的 [Program] 记录 *)
Fail Example p433_two_duals_not_convertible : VctDual359 F = Dual F := eq_refl.

(* control: objectwise, the carriers coincide on the nose / 控制：按对象，载体正好重合 *)
Example p433_carriers_convertible (x : Vct) :
  carrier (cmon_setoid (VctDual359 F x)) = carrier (cmon_setoid (Dual F x))
  := eq_refl.

(*
N5 CONVERSION: the packed modules do not — the proof fields of
   [HomMod] and [DualMod] are different opaque constants

--------
N5 转换：打包的模块不相同——[HomMod] 和 [DualMod] 的证明字段是不同的不透明常量
*)
Fail Example p433_objects_not_convertible (x : Vct) :
  (VctDual359 F x : Vct) = (Dual F x : Vct) := eq_refl.

(**
** B: TYPING — the refutation is conditional, and the self-adjunction
       has a direction

--------
** B：打字——反驳是有条件的，自我附加是有方向的
*)

(* control: the conditional statement / 控制：条件语句 *)
Check (dual_functor_no_right_adjoint F
         : CoordSpanProper F → ∀ Rt : Vct ⟶ Vct^op, Dual F ⊣ Rt → False).

(* N2 TYPING: the unconditional statement does not ascribe / N2 打字：无条件语句不归因于 *)
Fail Check (dual_functor_no_right_adjoint F
              : ∀ Rt : Vct ⟶ Vct^op, Dual F ⊣ Rt → False).

(* control: the self-adjunction, [(Dual F)^op ⊣ Dual F] / 控制：自我附着，[(Dual F)^op ⊣ Dual F] *)
Check (dual_vct_Adjunction F : Opposite_Functor (Dual F) ⊣ Dual F).

(* N3 TYPING: the exercise's direction is refused as an ascription / N3 输入：该练习的指示被拒绝作为归属 *)
Fail Check (dual_vct_Adjunction F : Dual F ⊣ Opposite_Functor (Dual F)).

(**
** C: the discrete diagram no longer pins [Set]

    RECORDED CORRECTION.  An earlier revision headed this section
    "UNIVERSE — the unannotated discrete diagram pins [Set]" and stated N4
    as a refusal: [DiscreteCat_Functor] made the shape's hom universe
    [Set], which no cocone in [Vct^op] could share, so the file's own
    [LineDiagram] had to be used instead.  The attribution was right and
    the donor was annotated in place in the PR "algebraic carriers are
    sets" (2026-09-17), Instance/Discrete.v; both lines are now
    accepted and are kept as positive controls at the same place.
    [LineDiagram] is retained because it names the diagram this file
    reasons about, not because [DiscreteCat_Functor] is unusable here.

--------
** C：该离散图不再固定 [Set]

已记录的更正。之前的一个修订版本在这一节的标题中写作“UNIVERSE — 未注释的离散图固定 [Set]”，并将 N4 作为拒绝：[DiscreteCat_Functor] 使形状的同类宇宙 [Set] 成立，而 [Vct^op] 中没有任何共锥可以共享，因此必须使用文件本身的 [LineDiagram]。归属是正确的，并且捐赠者在 PR “代数载体是集合”（2026-09-17），Instance/Discrete.v 中得到了就地注释；现在这两行均被接受，并作为阳性控制保留在同一位置。[LineDiagram] 被保留，因为它命名了该文件所推理的图，而不是因为 [DiscreteCat_Functor] 在这里不可用。
*)

(* control: the file's own diagram has cocones in [Vct^op] / 控制：该文件自身的图在 [Vct^op] 中有余顶 *)
Check (Cocone (LineDiagram F)).

(* former N4: so does the generic discrete diagram / 前N4：通用离散图也是如此 *)
Check (Cocone (DiscreteCat_Functor
                 (fun _ : nat => VctLine F : obj[Vct^op]))).

(** ** D: readbacks / ** D：复读 *)

Example p433_coord_component (n : nat) (v : carrier (cmon_setoid (PowLine F))) :
  cmon_map (rm_hom (vct_coord F n)) v = v n := eq_refl.

Example p433_prod_proj_component {R : RingObject} {I : Type}
  (V : I → RModObject R) (i : I) (f : carrier (cmon_setoid (ProdMod V))) :
  cmon_map (rm_hom (prod_proj V i)) f = f i := eq_refl.

Example p433_transpose_component {a x : Vct} (f : a ~{Vct}~> Dual F x)
  (v : carrier (cmon_setoid x)) (w : carrier (cmon_setoid a)) :
  cmon_map (rm_hom (cmon_map (rm_hom (vct_transpose F f)) v)) w
    = cmon_map (rm_hom (cmon_map (rm_hom f) w)) v := eq_refl.

(* the colimit mediator is the tuple of the competing cocone's legs / 余极限中介是竞争余锥的各腿的元组 *)
Example p433_mediator_component (M : Cocone (LineDiagram F))
  (z : carrier (cmon_setoid (vertex_obj[M] : Vct))) (n : nat) :
  cmon_map (rm_hom (unique_obj (PowCocone_IsColimitCocone F M))) z n
    = cmon_map (rm_hom (@vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)) z
  := eq_refl.

(* the isomorphism's components are the identity on functionals / 同构的分量在泛函上是恒等的 *)
Example p433_iso359_component (x : Vct) (g : carrier (cmon_setoid (Dual F x))) :
  cmon_map (rm_hom (to (projT1 (dual_iso359 F) x))) g = g := eq_refl.

(* the indexed-product record's mediator is the tuple / 被索引的产品记录的中介是元组 *)
Example p433_iprod_mediator {R : RingObject} {I : Type}
  (V : I → RModObject R) {Z : RModObject R} (pi : ∀ i, RModHom Z (V i)) :
  unique_obj (iprod_desc (ProdMod_IsIndexedProduct V) pi) = prod_tuple V pi
  := eq_refl.

Check (dual_vct_Continuous F : ContinuousFunctor (Dual F)).
Check (PowCocone_IsColimitCocone F).
Check (dual_not_left_adjoint_of_op F).
Check (dual359_not_left_adjoint_of_op F).
Check (@prod_tuple_proj).
Check (@prod_tuple_unique).
Check (@ProdMod_IsIndexedProduct).

End Probe.

(** ** Guard block / ** 防守格挡 *)

Check @Dual.
Check @VctDual359.
Check @VctSMC.
Check @dual_iso359.
Check @iso359.
Check @to359.
Check @from359.
Check @dual359_fmap_pre.
Check @dual359_no_right_adjoint.
Check @dual359_not_left_adjoint_of_op.
Check @adjunction_along_left_iso.
Check @ProdMod_IsIndexedProduct.
Check @IsIndexedProduct.
Check @iprod_desc.
Check @unique_obj.
Check @HomMod.
Check @DualMod.
Check @VctLine.
Check @PowLine.
Check @vct_coord.
Check @LineDiagram.
Check @CoordSpanProper.
Check @dual_functor_no_right_adjoint.
Check @dual_vct_Adjunction.
Check @dual_vct_AdjointOnTheRight.
Check @vct_transpose.
Check @ProdMod.
Check @prod_proj.
Check @dual.
Check @dual_self_adjoint_on_the_right.
Check @RMod_SymMonClosed.
Check @DiscreteCat_Functor.
Check @DiscreteCat_Functor'.
Check @Cocone.
Check @Opposite_Functor.
Check @Vct_F.
Check @FieldObject.
Check @field_ring.
Check @field_comm.
Check @SymMonClosed.
Check @AdjointOnTheRight.
Check @Adjunction.
Check @ContinuousFunctor.
Check @cmon_map.
Check @rm_hom.
Check @cmon_setoid.
Check @carrier.
Check @RModObject.
Check @RingObject.
Check nat.
