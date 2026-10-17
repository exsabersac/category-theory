(*
   本文件为测试：ProbeRepresentability437。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.
Require Import Category.Adjunction.Representability.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe437_absent_name.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Check (fun (C : Category) (K : C ⟶ Sets) => @sols_of_esols C K).
Check (fun (C : Category) (K : C ⟶ Sets) => @esols_of_sols C K).

Example p437_index (C : Category) (K : C ⟶ Sets) (E : ElementSolutionSet K) :
  sol_index (sols_of_esols K E) = esol_index E := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p437_same_record (C : Category) (K : C ⟶ Sets) :
  ElementSolutionSet K = SolutionSet K SetsOne := eq_refl.

(* control: [HomAfter K 1] IS 复合 points 函子 （已译） *)
Example p437_homafter (C : Category) (K : C ⟶ Sets) :
  HomAfter K SetsOne = Compose (fobj[Curried_Hom Sets] SetsOne) K := eq_refl.

(* N2 CONVERSION: it is not [K] itself — [homafter_one_iso] is needed *)
Fail Example p437_homafter_is_K (C : Category) (K : C ⟶ Sets) :
  HomAfter K SetsOne = K := eq_refl.

(* 相关说明。 （已译） *)

(* control: the theorem at its stated hypotheses *)
Check (fun (C : Category) (K : C ⟶ Sets) (comp : @Complete C)
           (cont : @PreservesImageLimit C Sets K) (E : ElementSolutionSet K) =>
         representability_theorem K comp cont E).

(* 相关说明。 （已译） *)
Fail Check (fun (C : Category) (K : C ⟶ Sets) (comp : @Complete C)
                (cont : @PreservesAllLimits C Sets K)
                (E : ElementSolutionSet K) =>
              representability_theorem K comp cont E).

(* control: the copower hypothesis, indexed by an object of [Sets] *)
Check (fun (C : Category) => HasSetsCopowers C).

(* 相关说明。 （已译） *)
Fail Definition p437_type_copowers (C : Category)
  (cop : ∀ (b : C) (X : Type),
      Representable (HomAfter (fobj[@Curried_Hom C] b) X))
  : HasSetsCopowers C := cop.

(* * ** C: UNIVERSE — 定理 inherits GAFT's pin （已译） *)

Section Formability.

Universes so sh sp.
Constraint sh < sp.

Context (Cu : Category@{so sh sp}).

(* control: 范畴 itself formable, so homs （已译） *)
Check (@hom Cu).

(* N4 UNIVERSE: 定理's comma-initial step identifies hom 证明,
 so it cannot read at [Cu] （已译） *)
Fail Check (fun (K : Cu ⟶ Sets) (comp : @Complete Cu)
                (cont : @PreservesImageLimit Cu Sets K)
                (E : ElementSolutionSet K) =>
              representability_theorem K comp cont E).

End Formability.

(** ** D: readbacks *)

Example p437_esol_obj (C : Category) (K : C ⟶ Sets) (E : ElementSolutionSet K)
  (i : esol_index E) : sol_obj (sols_of_esols K E) i = esol_obj E i := eq_refl.

Example p437_esols_elem (C : Category) (K : C ⟶ Sets)
  (S : SolutionSet K SetsOne) (i : sol_index S) :
  esol_elem (esols_of_sols K S) i = sol_arr S i ttt := eq_refl.

Example p437_transport_obj (C : Category) (F G : C ⟶ Sets)
  (i : F ≅[[C, Sets]] G) (R : Representable F) :
  @repr_obj C G (Representable_transport i R) = @repr_obj C F R := eq_refl.

Example p437_left_adjoint_obj (C : Category) (K : C ⟶ Sets) (L : Sets ⟶ C)
  (A : L ⊣ K) :
  @repr_obj C K (representable_of_left_adjoint K A) = L SetsOne := eq_refl.

Example p437_sets_id_obj :
  @repr_obj Sets (@Id Sets) Sets_Id_repr_of_adjoint
    = projT1 GAFT_at_Sets_Id SetsOne := eq_refl.

Check (Sets_points_esol_obj).
Check (Sets_points_iso
         : @repr_obj Sets Sets_points Sets_points_repr ≅ SetsOne).
Check (Sets_Id_repr_iso
         : @repr_obj Sets (@Id Sets) Sets_Id_repr ≅ SetsOne).
Check (@representability_iff).
Check (@saft_representable).
Check (@left_adjoint_of_representable_Sets).

(** ** Guard block *)

Check @ElementSolutionSet.
Check @esol_index.
Check @esol_obj.
Check @esol_elem.
Check @esol_covers.
Check @sols_of_esols.
Check @esols_of_sols.
Check @representable_of_comma_initial.
Check @representability_theorem.
Check @representability_iff.
Check @Representable_transport.
Check @homafter_one_iso.
Check @representable_of_left_adjoint.
Check @continuous_of_representable.
Check @preserves_image_of_representable.
Check @saft_representable.
Check @HasSetsCopowers.
Check @homafter_whisker.
Check @left_adjoint_of_representable_Sets.
Check @comma_initial_of_sols.
Check @GAFT_via_comma_initial.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @Representable.
Check @repr_obj.
Check @represented.
Check @HomAfter.
Check @Curried_Hom.
Check @global_element.
Check @PreservesImageLimit.
Check @PreservesAllLimits.
Check @Complete.
Check @SetsOne.
Check @Sets_points.
Check @Sets_points_repr.
Check @Sets_Id_repr.
Check @Sets_Id_repr_of_adjoint.
Check @GAFT_at_Sets_Id.
