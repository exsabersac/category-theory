(*
   本文件为测试：ProbeGAFTCharacterization436。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe436_absent_name.

(* 相关说明。 （已译） *)

Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @sol_covers.

(* 相关说明。 （已译） *)
Fail Check @sol_unique.

(* 相关说明。 （已译） *)

Section Conversion.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (d : D).

Example p436_index : sol_index (solution_set_of_adjunction A d) = poly_unit
  := eq_refl.

Example p436_obj (u : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) u = F d := eq_refl.

Example p436_arr (u : poly_unit) :
  sol_arr (solution_set_of_adjunction A d) u = @unit _ _ _ _ A d := eq_refl.

(* 相关说明。 （已译） *)
Example p436_via_index :
  sol_index (solution_set_of_adjunction_via_comma A d)
    = sol_index (solution_set_of_adjunction A d) := eq_refl.

Example p436_via_obj (u : poly_unit) :
  sol_obj (solution_set_of_adjunction_via_comma A d) u = F d := eq_refl.

Example p436_via_arr (u : poly_unit) :
  sol_arr (solution_set_of_adjunction_via_comma A d) u = @unit _ _ _ _ A d
  := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p436_routes_agree :
  solution_set_of_adjunction A d = solution_set_of_adjunction_via_comma A d
  := eq_refl.

(* n8 CONVERSION: the member is [F d], not [F (U (F d))] *)
Fail Example p436_member_is_FUF (u : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) u = F (U (F d)) := eq_refl.

(* 相关说明。 （已译） *)
Example p436_wif_index (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = wif_index W := eq_refl.

(* n3 CONVERSION: so a general solution set is not a singleton *)
Fail Example p436_general_is_singleton (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = poly_unit := eq_refl.

End Conversion.

(* 相关说明。 （已译） *)

Check (fun (C D : Category) (U : C ⟶ D) (comp : @Complete C)
           (cont : @PreservesImageLimit C D U)
           (sols : ∀ d : D, SolutionSet U d) => GAFT U comp cont sols).

(* n4 TYPING: completeness and a solution set alone do not ascribe *)
Fail Check (fun (C D : Category) (U : C ⟶ D) (comp : @Complete C)
                (sols : ∀ d : D, SolutionSet U d) => GAFT U comp sols).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Monomorphic Universes p436o p436h p436p.
Monomorphic Constraint Set < p436h.

(*
   本节说明 ProbeGAFTCharacterization436 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* control: necessity is free of the pin *)
Check (fun (Cu : Category@{p436o p436h p436p}) (Du : Category@{p436o p436h p436p})
           (F : Du ⟶ Cu) (U : Cu ⟶ Du) => @solution_set_of_adjunction Cu Du F U).

(* former n6: the biconditional is accepted there too *)
Check (fun (Cu : Category@{p436o p436h p436p})
                (Du : Category@{p436o p436h p436p})
                (U : Cu ⟶ Du) => @GAFT_iff Cu Du U).

(* 相关说明。 （已译） *)

Example p436_rev_is_GAFT {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (cont : @PreservesImageLimit C D U) (sols : ∀ d : D, SolutionSet U d) :
  GAFT_iff_rev U comp (cont, sols) = GAFT U comp cont sols := eq_refl.

Example p436_sets_rev :
  Sets_Id_has_left = GAFT_at_Sets_Id := eq_refl.

Example p436_sets_index (d : Sets) :
  sol_index (solution_set_of_adjunction (@adj_id Sets) d)
    = sol_index (Sets_Id_SolutionSet d) := eq_refl.

Example p436_sets_obj (d : Sets) (u : poly_unit) :
  sol_obj (solution_set_of_adjunction (@adj_id Sets) d) u
    = sol_obj (Sets_Id_SolutionSet d) u := eq_refl.

Example p436_sets_arr (d : Sets) (u : poly_unit) :
  sol_arr (solution_set_of_adjunction (@adj_id Sets) d) u
    = sol_arr (Sets_Id_SolutionSet d) u := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p436_sets_same_record (d : Sets) :
  solution_set_of_adjunction (@adj_id Sets) d = Sets_Id_SolutionSet d
  := eq_refl.

(** ** F: guard block *)

Check @solution_set_of_adjunction.
Check @solution_set_of_adjunction_index.
Check @solution_set_of_adjunction_obj.
Check @solution_set_of_adjunction_arr.
Check @universal_arrow_of_adjunction.
Check @comma_initial_of_adjunction.
Check @solution_set_of_adjunction_via_comma.
Check @solution_set_via_comma_index.
Check @solution_set_via_comma_obj.
Check @solution_set_via_comma_arr.
Check @comma_Complete_via_creation.
Check @GAFT_iff.
Check @GAFT_iff_fwd.
Check @GAFT_iff_rev.
Check @GAFT_iff_rev_is_GAFT.
Check @GAFT_iff_at_Sets_Id.
Check @Sets_Id_has_left.
Check @Sets_Id_has_left_is_GAFT_at_Sets_Id.
Check @Sets_Id_SolutionSet_of_adjunction.
Check @Sets_Id_sols_index.
Check @Sets_Id_sols_obj.
Check @Sets_Id_sols_arr.
Check @GAFT.
Check @GAFT_from_initials.
Check @GAFT_via_comma_initial.
Check @comma_initial_of_sols.
Check @sols_of_wif.
Check @SolutionSet.
Check @right_adjoint_PreservesImageLimit.
Check @Sets_Id_SolutionSet.
Check @Sets_Id_PreservesImageLimit.
Check @GAFT_at_Sets_Id.
