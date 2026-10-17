(*
   本文件为测试：ProbeHomContinuous428。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.End.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Functor.Hom.Continuous.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe428_absent_name.

(* * ** A: two presentations hom-diagram agree 对象 on
 action [fmap], not at [fmap] field （已译） *)

Section Presentations.

Context {J C : Category} (c : C) (F : J ⟶ C).

(* controls: 对象, action element, both convert （已译） *)
Example p428_fobj : fobj[@HomFrom C c ◯ F] = fobj[HomDiagram c F] := eq_refl.

Example p428_fmap_value {j j' : J} (g : j ~{J}~> j') (h : c ~{C}~> F j) :
  fmap[@HomFrom C c ◯ F] g h = fmap[HomDiagram c F] g h := eq_refl.

(* N1 CONVERSION: whole [fmap] field does not — setoid 态射's
 respectfulness 证明 is opaque [Program] obligation:
 [Curried_Hom_obligation_1], auto-discharged Functor/Hom.v, against
 [HomDiagram]'s written-out one Structure/Limit/Weighted.v（已译） *)
Fail Example p428_fmap_field {j j' : J} (g : j ~{J}~> j') :
  fmap[@HomFrom C c ◯ F] g = fmap[HomDiagram c F] g := eq_refl.

(* 相关说明。 （已译） *)
Example p428_image_apex (N : Cone F) :
  carrier (vertex_obj[FCone (@HomFrom C c) N]) = (c ~{C}~> vertex_obj[N])
  := eq_refl.

Example p428_limit_carrier :
  carrier (Sets_limit_obj (HomDiagram c F)) = Sets_limit_carrier (HomDiagram c F)
  := eq_refl.

Example p428_cone_carrier :
  carrier (fobj[ConePresheaf F] c) = @ACone J C c F := eq_refl.

End Presentations.

(* 相关说明。 （已译） *)

Section Universes.

Universe o1 h1 hbig sbig.
Constraint h1 < hbig.
Constraint hbig < sbig.

Context (Cw : Category@{o1 h1 h1}) (cw : Cw).

(* control: level universe HOLDING Sets' 对象 free above
 carrier level ([Sets@{o so} : Category@{so o o}], Instance/Sets.v) （已译） *)
Check (@HomFrom Cw cw : Cw ⟶ Sets@{h1 sbig}).
Check (@hom_continuous_at Cw cw
       : ContinuousFunctor (@HomFrom_at Cw cw : Cw ⟶ Sets@{h1 sbig})).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@HomFrom Cw cw : Cw ⟶ Sets@{hbig sbig}).

End Universes.

(* * ** C: smallness — Remark 2's [Sets]-side limit needs shape's 对象
 at below carrier level; #331's 定理 does not （已译） *)

Section Smallness.

Universe jo h.
Constraint h < jo.

Context (Jw : Category@{jo h h}) (Cw : Category@{h h h}) (cw : Cw).

(* 相关说明。 （已译） *)
Check (fun F : Jw ⟶ Cw => @HomFrom Cw cw ◯ F).
Check (fun F : Jw ⟶ Cw => hom_PreservesLimitCone cw F).

(* N3 UNIVERSE: [Sets] limit hom-diagram refused —
 [Sets_Limit] needs shape's 对象 level at below [Sets]' carrier
 level, here [h] （已译） *)
Fail Check (fun F : Jw ⟶ Cw => Sets_Limit (@HomFrom Cw cw ◯ F)).

End Smallness.

(** ** D: readbacks *)

Section Readbacks.

Context {J C : Category} {F : J ⟶ C} (L : Limit F) (c : C).

Check (remark2_iso L c).
Check (remark2_natural L).
Check (remark2_comparison_iso L c).
Check (end_Limit c F).
Check (cone_nat_iso (F:=F) c).
Check (limtuple_cone_iso (F:=F) c).

(* 相关说明。 （已译） *)
Check (hom_preserves_limits c).
Check (@cohom_carries_colimits_to_limits C c).

End Readbacks.

(** ** Guard block *)

Check @HomFrom.
Check @HomTo.
Check @HomDiagram.
Check @Sets_Limit.
Check @Sets_limit_obj.
Check @Sets_limit_carrier.
Check @ConePresheaf.
Check @ACone.
Check @FCone.
Check @Cone.
Check @Limit.
Check @hom_PreservesLimitCone.
Check @hom_ContinuousFunctor.
Check @hom_continuous_at.
Check @HomFrom_at.
Check @PreservesLimitCone_transport.
Check @ContinuousFunctor_transport.
Check @remark2_iso.
Check @remark3_iso.
Check @hom_iprod_iso.
Check @cohom_icoprod_iso.
Check @end_Limit.
Check @fmap.
Check @fobj.
Check @carrier.
Check @vertex_obj.
