(*
   本文件为测试：ProbeDualNoRightAdjoint433。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* instrument: the refutation keyword is live *)
Fail Check probe433_absent_name.

Section Probe.

Context (F : FieldObject).

Notation Vct := (Vct_F F).

(** ** A: CONVERSION — two dual functors, naturally isomorphic, not
       convertible *)

(* control: #359's headline, Structure/Monoidal/Dual.v's self-adjunction
   on the right, instantiates at the target's reading of [dual] *)
Definition p433_dual359_self_right :
  @AdjointOnTheRight Vct Vct (VctDual359 F) (VctDual359 F) :=
  @dual_self_adjoint_on_the_right Vct (VctSMC F) (VctLine F).

(* control: the isomorphism is delivered, and the exercise holds for the
   functor the issue names *)
Check (dual_iso359 F : Dual F ≈ VctDual359 F).
Check (dual359_no_right_adjoint F
         : CoordSpanProper F → ∀ Rt : Vct ⟶ Vct^op, VctDual359 F ⊣ Rt → False).

(* N1 CONVERSION: the two functors are different [Program] records *)
Fail Example p433_two_duals_not_convertible : VctDual359 F = Dual F := eq_refl.

(* control: objectwise, the carriers coincide on the nose *)
Example p433_carriers_convertible (x : Vct) :
  carrier (cmon_setoid (VctDual359 F x)) = carrier (cmon_setoid (Dual F x))
  := eq_refl.

(* N5 CONVERSION: the packed modules do not — the proof fields of
   [HomMod] and [DualMod] are different opaque constants *)
Fail Example p433_objects_not_convertible (x : Vct) :
  (VctDual359 F x : Vct) = (Dual F x : Vct) := eq_refl.

(** ** B: TYPING — the refutation is conditional, and the self-adjunction
       has a direction *)

(* control: the conditional statement *)
Check (dual_functor_no_right_adjoint F
         : CoordSpanProper F → ∀ Rt : Vct ⟶ Vct^op, Dual F ⊣ Rt → False).

(* N2 TYPING: the unconditional statement does not ascribe *)
Fail Check (dual_functor_no_right_adjoint F
              : ∀ Rt : Vct ⟶ Vct^op, Dual F ⊣ Rt → False).

(* control: the self-adjunction, [(Dual F)^op ⊣ Dual F] *)
Check (dual_vct_Adjunction F : Opposite_Functor (Dual F) ⊣ Dual F).

(* N3 TYPING: the exercise's direction is refused as an ascription *)
Fail Check (dual_vct_Adjunction F : Dual F ⊣ Opposite_Functor (Dual F)).

(** ** C: the discrete diagram no longer pins [Set]

    RECORDED CORRECTION.  An earlier revision headed this section
    "UNIVERSE — the unannotated discrete diagram pins [Set]" and stated N4
    as a refusal: [DiscreteCat_Functor] made the shape's hom universe
    [Set], which no cocone in [Vct^op] could share, so the file's own
    [LineDiagram] had to be used instead.  The attribution was right and
    the donor was annotated in place in the PR "algebraic carriers are
    sets" (2026-09-17), Instance/Discrete.v; both lines are now
    accepted and are kept as positive controls at the same place.
    [LineDiagram] is retained because it names the diagram this file
    reasons about, not because [DiscreteCat_Functor] is unusable here. *)

(* control: the file's own diagram has cocones in [Vct^op] *)
Check (Cocone (LineDiagram F)).

(* former N4: so does the generic discrete diagram *)
Check (Cocone (DiscreteCat_Functor
                 (fun _ : nat => VctLine F : obj[Vct^op]))).

(** ** D: readbacks *)

Example p433_coord_component (n : nat) (v : carrier (cmon_setoid (PowLine F))) :
  cmon_map (rm_hom (vct_coord F n)) v = v n := eq_refl.

Example p433_prod_proj_component {R : RingObject} {I : Type}
  (V : I → RModObject R) (i : I) (f : carrier (cmon_setoid (ProdMod V))) :
  cmon_map (rm_hom (prod_proj V i)) f = f i := eq_refl.

Example p433_transpose_component {a x : Vct} (f : a ~{Vct}~> Dual F x)
  (v : carrier (cmon_setoid x)) (w : carrier (cmon_setoid a)) :
  cmon_map (rm_hom (cmon_map (rm_hom (vct_transpose F f)) v)) w
    = cmon_map (rm_hom (cmon_map (rm_hom f) w)) v := eq_refl.

(* the colimit mediator is the tuple of the competing cocone's legs *)
Example p433_mediator_component (M : Cocone (LineDiagram F))
  (z : carrier (cmon_setoid (vertex_obj[M] : Vct))) (n : nat) :
  cmon_map (rm_hom (unique_obj (PowCocone_IsColimitCocone F M))) z n
    = cmon_map (rm_hom (@vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)) z
  := eq_refl.

(* the isomorphism's components are the identity on functionals *)
Example p433_iso359_component (x : Vct) (g : carrier (cmon_setoid (Dual F x))) :
  cmon_map (rm_hom (to (projT1 (dual_iso359 F) x))) g = g := eq_refl.

(* the indexed-product record's mediator is the tuple *)
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

(** ** Guard block *)

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
