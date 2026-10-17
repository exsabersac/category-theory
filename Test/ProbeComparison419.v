(*
   本文件为测试：ProbeComparison419。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* instrument: the refutation keyword is live *)
Fail Check probe419_absent_name.

(** ** A: the two bracketings of a twice-reindexed cone are distinct types *)

Section Bracketing.

Context {J'' J' J C : Category} (W : J' ⟶ J) (V : J'' ⟶ J') {F : J ⟶ C}.

(* control: at its own bracketing *)
Check (fun N : Cone F =>
         (cone_reindex V (cone_reindex W N) : Cone ((F ◯ W) ◯ V))).

(* control: repackaged field by field, it is a cone at the other one *)
Check (fun N : Cone F =>
         (cone_assoc (cone_reindex V (cone_reindex W N)) : Cone (F ◯ (W ◯ V)))).

(* N1 CONVERSION: not by conversion *)
Fail Check (fun N : Cone F =>
              (cone_reindex V (cone_reindex W N) : Cone (F ◯ (W ◯ V)))).

(* readbacks: apex and legs agree at [eq_refl] across the two bracketings *)
Check (@cone_reindex_comp_apex J'' J' J C W V F).
Check (@cone_reindex_comp_leg J'' J' J C W V F).

End Bracketing.

(** ** B: the former [Set] pin of the discrete-diagram functor, lifted *)

Section SetPin.

Universe uo uh.
Constraint Set < uh.

Context (Cu Du : Category@{uo uh uh}) (Fu : Cu ⟶ Du) (fam : bool → Cu)
        (HC : @Cartesian Cu) (HD : @Cartesian Du).

(* control (a): the cone type over the unannotated functor is formable *)
Check (fun N : Cone (@DiscreteCat_Functor bool Cu fam) => N).

(* control (b): the comparison at the annotated functor *)
Check (fun (N : Cone (@DiscreteCat_Functor' bool Cu fam))
           (M : Cone (Fu ◯ @DiscreteCat_Functor' bool Cu fam))
           (HM : IsLimitCone M) =>
         cone_comparison Fu N HM).

(* control (c): the elementary binary comparison *)
Check (@binary_comparison Cu Du Fu HC HD fam).

(* Former N2, now a positive control: the comparison at the annotated
   functor.  RECORDED CORRECTION -- see the header. *)
Check (fun (N : Cone (@DiscreteCat_Functor bool Cu fam))
                (M : Cone (Fu ◯ @DiscreteCat_Functor bool Cu fam))
                (HM : IsLimitCone M) =>
              cone_comparison Fu N HM).

(* Former N3, now a positive control: Structure/Limit/Product.v's
   [family_cone] feeds it too.  RECORDED CORRECTION -- see the header. *)
Check (fun (c : Cu) (pi : ∀ b : bool, c ~{Cu}~> fam b)
                (M : Cone (Fu ◯ @DiscreteCat_Functor bool Cu fam))
                (HM : IsLimitCone M) =>
              cone_comparison Fu (family_cone fam c pi) HM).

End SetPin.

(** ** C: the orientation of [TerminalFunctor]'s comparison *)

Section Orientation.

Context {C D : Category} (F : C ⟶ D) `{@Terminal C} `{@Terminal D}.

(* control: the comparison direction is the class's [from] *)
Check (fun HF : @TerminalFunctor C D F _ _ =>
         (from (@fobj_one_iso _ _ F _ _ HF) : F terminal_obj ~{D}~> terminal_obj)).

(* N4 TYPING: [to] is oriented the other way *)
Fail Check (fun HF : @TerminalFunctor C D F _ _ =>
              (to (@fobj_one_iso _ _ F _ _ HF) : F terminal_obj ~{D}~> terminal_obj)).

(* readback: the comparison is the unique map into [1] *)
Check (terminal_comparison_one F nullary_fam).

End Orientation.

(** ** D: the limit comparison does not read a cocone without repackaging *)

Section OpRoute.

Context {J C D : Category} {K : J ⟶ C} (F : C ⟶ D).

(* control: the cocone comparison *)
Check (fun (N : Cocone K) (M : Cocone (F ◯ K)) (HM : IsColimitCocone M) =>
         cocone_comparison F N HM).

(* control: the op route, once [M] is repackaged by [cone_op_comp] *)
Check (fun (N : Cocone K) (M : Cocone (F ◯ K)) (HM : IsColimitCocone M) =>
         cone_comparison (F^op) N (islimitcone_op_comp HM)).

(* N5 TYPING: the op route on the cocone as it stands *)
Fail Check (fun (N : Cocone K) (M : Cocone (F ◯ K)) (HM : IsColimitCocone M) =>
              cone_comparison (F^op) N HM).

End OpRoute.

(** ** E: readbacks and positive formability *)

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

(** ** Guard block *)

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
