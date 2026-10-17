(*
   本文件为测试：ProbeGrpFreeAFT442。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.FreeAFT.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe442_absent_name.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p442_instrument :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable = SetOne := eq_refl.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The theorem is applied to exactly these four arguments. *)
Example p442_via_GAFT_is_GAFT :
  free_group_via_GAFT_from_adjunction
    = GAFT Grp_Forget Grp_Complete
           (Continuous_PreservesImageLimit Grp_Forget_continuous)
           Grp_Forget_solution_set_from_adjunction := eq_refl.

(* THE CIRCULARITY, [eq_refl]. The third 假设 fed Freyd's
 定理 singleton family at unit 伴随 the
 定理 meant produce. （已译） *)
Example p442_solution_set_is_circular (X : Sets) :
  Grp_Forget_solution_set_from_adjunction X
    = solution_set_of_adjunction free_group_adjunction X := eq_refl.

Example p442_sol_index (X : Sets) :
  sol_index (Grp_Forget_solution_set_from_adjunction X) = poly_unit := eq_refl.

(* 相关说明。 （已译） *)
Example p442_sol_obj (X : Sets) (i : poly_unit) :
  sol_obj (Grp_Forget_solution_set_from_adjunction X) i = FreeGrpObject X
  := eq_refl.

Example p442_sol_arr (X : Sets) (i : poly_unit) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i = free_group_unit X
  := eq_refl.

(* control N4: arrow 嵌入 generators agree at every
 point, Instance/Grp/Free.v's [free_group_unit_is_insert]. （已译） *)
Example p442_sol_arr_pointwise (X : Sets) (i : poly_unit) (a : carrier X) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i a = fg_insert X a
  := eq_refl.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p442_sol_arr_is_insert (X : Sets) (i : poly_unit) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i = fg_insert X
  := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Check (free_group_via_GAFT_agrees : `1 free_group_via_GAFT ≈ FreeGrp).

(* ...and it is [left_adjoint_iso] applied, nothing instance-specific. *)
Example p442_agrees_is_generic :
  free_group_via_GAFT_agrees
    = left_adjoint_iso Grp_Forget _ FreeGrp (`2 free_group_via_GAFT)
                       free_group_adjunction := eq_refl.

(* N1 CONVERSION: two 函子 NOT convertible. [GAFT] is
 [Qed]-opaque, so output does not reduce at all. （已译） *)
Fail Example p442_gaft_output_is_FreeGrp :
  `1 free_group_via_GAFT = FreeGrp := eq_refl.

(* N2 CONVERSION: nor at single 对象 — not even at singleton, where
 free group one-generator group representation uses. （已译） *)
Fail Example p442_gaft_output_obj :
  `1 free_group_via_GAFT SetOne = FreeGrpObject SetOne := eq_refl.

(* N3 TYPE: two 伴随 not comparable [=] at all, their
 left legs being different terms. （已译） *)
Fail Example p442_gaft_adjunction_is_free :
  `2 free_group_via_GAFT = free_group_adjunction := eq_refl.

(* 相关说明。 （已译） *)

(* control: the application, again, as a [Check] *)
Check (GAFT Grp_Forget Grp_Complete
            (Continuous_PreservesImageLimit Grp_Forget_continuous)
            Grp_Forget_solution_set_from_adjunction).

(* 相关说明。 （已译） *)
Fail Check (GAFT Grp_Forget Grp_Complete Grp_Forget_continuous
                 Grp_Forget_solution_set_from_adjunction).

(* 相关说明。 （已译） *)
Fail Check (GAFT Grp_Forget Grp_Complete Grp_Forget_PreservesAllLimits
                 Grp_Forget_solution_set_from_adjunction).

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p442_GAFT_at_Grp :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous).

(* 相关说明。 （已译） *)
Definition p442_sols_indexed_by (I : Type)
  (o : ∀ X : Sets, I → Grp)
  (a : ∀ (X : Sets) (i : I), X ~{Sets}~> Grp_Forget (o X i))
  (cov : ∀ (X : Sets) (c : Grp) (h : X ~{Sets}~> Grp_Forget c),
      { i : I & { t : o X i ~{Grp}~> c & fmap[Grp_Forget] t ∘ a X i ≈ h } })
  (X : Sets) : SolutionSet Grp_Forget X :=
  {| sol_index := I
   ; sol_obj := o X
   ; sol_arr := a X
   ; sol_covers := fun c h => cov X c h |}.

(* control: at [Set]-level index builder's output IS what [GAFT]
 所消耗 at instance. （已译） *)
Check (fun o a cov =>
         p442_GAFT_at_Grp (p442_sols_indexed_by bool o a cov)).

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (G : Grp) o a cov =>
         p442_GAFT_at_Grp (p442_sols_indexed_by (Subgroup G) o a cov)).

(** ** E: the induced monad *)

Example p442_ret_is_unit (X : Sets) :
  @ret Sets _ free_group_monad X = free_group_unit X := eq_refl.

Example p442_ret_generator (X : Sets) (a : carrier X) :
  @ret Sets _ free_group_monad X a = fg_insert X a := eq_refl.

Example p442_join_is_counit (X : Sets) :
  @join Sets _ free_group_monad X
    = fmap[Grp_Forget] (free_group_counit (FreeGrp X)) := eq_refl.

Example p442_monad_functor_obj (X : Sets) :
  fobj[Grp_Forget ◯ FreeGrp] X = grp_setoid (FreeGrpObject X) := eq_refl.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p442_join_is_word_evaluation (X : Sets) :
  @join Sets _ free_group_monad X
    = fmap[Grp_Forget]
        (free_grp_extend (@id Sets (Grp_Forget (FreeGrp X)))) := eq_refl.

(* 相关说明。 （已译） *)

Example p442_repr_obj :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable = FreeGrp SetOne
  := eq_refl.

Example p442_repr_obj_word :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable
    = FreeGrpObject unit_setoid_object := eq_refl.

Example p442_repr_to_component (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  transform[to (@represented Grp Grp_Forget Grp_Forget_Representable)] G f
    = grp_repr_to G f := eq_refl.

Example p442_repr_from_component (G : Grp) (a : carrier (Grp_Forget G)) :
  transform[from (@represented Grp Grp_Forget Grp_Forget_Representable)] G a
    = grp_repr_from G a := eq_refl.

Example p442_repr_to_is_transpose (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  grp_repr_to G f = to (grp_adj G) f ttt := eq_refl.

(* 相关说明。 （已译） *)
Lemma p442_repr_to_from (G : Grp) (a : carrier (Grp_Forget G)) :
  grp_repr_to G (grp_repr_from G a) ≈ a.
Proof. exact (iso_to_from (grp_adj G) (grp_repr_const G a) ttt). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem p442_repr_separates :
  grp_repr_from Z2 true ≈ grp_repr_from Z2 false → False.
Proof.
  intro H.
  apply Z2_nontrivial.
  transitivity (grp_repr_to Z2 (grp_repr_from Z2 true)).
  - symmetry; exact (p442_repr_to_from Z2 true).
  - transitivity (grp_repr_to Z2 (grp_repr_from Z2 false)).
    + exact (proper_morphism (to (grp_adj Z2)) _ _ H ttt).
    + exact (p442_repr_to_from Z2 false).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem p442_repr_obj_not_trivial :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable ≅[Grp] Grp_trivial
    → False.
Proof.
  intro i.
  apply p442_repr_separates.
  transitivity (grp_repr_from Z2 true ∘ (from i ∘ to i)).
  - rewrite iso_from_to; rewrite id_right; reflexivity.
  - transitivity (grp_repr_from Z2 false ∘ (from i ∘ to i)).
    + rewrite !comp_assoc.
      rewrite (Grp_zero_hom_unique Z2
                 (grp_repr_from Z2 true ∘ from i)
                 (grp_repr_from Z2 false ∘ from i)).
      reflexivity.
    + rewrite iso_from_to; rewrite id_right; reflexivity.
Qed.

(** ** G: guard block *)

Check @Grp_Forget_solution_set_from_adjunction.
Check @free_group_via_GAFT.
Check @free_group_via_GAFT_agrees.
Check @free_group_monad.
Check @grp_repr_const.
Check @grp_repr_to.
Check @grp_repr_from.
Check @grp_repr_to_natural.
Check @grp_repr_from_natural.
Check @Grp_Forget_Representable.
Check @GAFT.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @sol_covers.
Check @solution_set_of_adjunction.
Check @Continuous_PreservesImageLimit.
Check @Adjunction_Induced_Monad.
Check @left_adjoint_iso.
Check @Representable.
Check @repr_obj.
Check @represented.
Check @Grp.
Check @Grp_Forget.
Check @Grp_Complete.
Check @Grp_Forget_continuous.
Check @Grp_Forget_PreservesAllLimits.
Check @Grp_trivial.
Check @Grp_zero_hom_unique.
Check @Z2.
Check @Z2_nontrivial.
Check @Subgroup.
Check @FreeGrp.
Check @FreeGrpObject.
Check @free_group_adjunction.
Check @free_group_unit.
Check @free_group_counit.
Check @free_grp_extend.
Check @fg_insert.
Check @unit_setoid_object.

Check @p442_GAFT_at_Grp.
Check @p442_sols_indexed_by.
Check @p442_repr_to_from.
Check @p442_repr_separates.
Check @p442_repr_obj_not_trivial.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The 推论's statement tree's own, converted: [free_group_unit]
 IS [fg_insert] at generator, so general result not weaker
 restatement Instance/Grp/Free.v. （已译） *)
Example p442_two_letters_same_statement :
  (free_group_unit TwoLetters true ≈ free_group_unit TwoLetters false → False)
  = (fg_insert TwoLetters true ≈ fg_insert TwoLetters false → False)
  := eq_refl.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p442_two_letters_same_proof :
  free_group_two_letters_distinct = free_group_two_generators_distinct
  := eq_refl.

(* N10 TYPE: decision procedure real 论元, not inferable
 one. Dropping it leaves two elements where [SetoidDecidable X] is
 expected. （已译） *)
Fail Check (fun (X : Sets) (a b : carrier X) =>
              free_group_unit_injective_dec (X:=X) a b).

Check @free_group_transpose_at_unit.
Check @free_group_unit_injective_of_embedding.
Check @free_group_unit_injective_dec.
Check @free_group_two_letters_distinct.
Check @free_group_two_generators_distinct.
Check @SetoidDecidable.
Check @grp_chi.
Check @TwoLetters.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @IsGrpCongruence.
Check @FGCongIdx.
Check @QGrp_Setoid.
Check @QGrp.
Check @QGrp_insert.
Check @fg_ev.
Check @fg_ker.
Check @fg_ker_is_cong.
Check @fg_ker_idx.
Check @fg_ker_med.
Check @QGrpOf.
Check @QGrpInsertOf.
Check @Grp_Forget_solution_set_prop.
Check @free_group_via_GAFT_from_adjunction.
Check @free_group_monad_via_GAFT.

(* 相关说明。 （已译） *)
Example p442_via_GAFT_prop_is_GAFT :
  free_group_via_GAFT
    = GAFT Grp_Forget Grp_Complete
           (Continuous_PreservesImageLimit Grp_Forget_continuous)
           Grp_Forget_solution_set_prop := eq_refl.

Section PropSolutionReadbacks.

Context (X : Sets).

(* The index IS congruence type, members ARE quotients, the
 arrows ARE 嵌入 generators them. （已译） *)
Example p442_sol_prop_index :
  sol_index (Grp_Forget_solution_set_prop X) = FGCongIdx X := eq_refl.

Example p442_sol_prop_obj (i : FGCongIdx X) :
  sol_obj (Grp_Forget_solution_set_prop X) i = QGrp (`1 i) (`2 i) := eq_refl.

Example p442_sol_prop_arr (i : FGCongIdx X) :
  sol_arr (Grp_Forget_solution_set_prop X) i = QGrp_insert (`1 i) (`2 i)
  := eq_refl.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p442_sol_prop_carrier (i : FGCongIdx X) :
  carrier (grp_setoid (sol_obj (Grp_Forget_solution_set_prop X) i)) = FGWord X
  := eq_refl.

(* 相关说明。 （已译） *)
Example p442_ker_idx_is_kernel (G : Grp) (h : X ~{Sets}~> Grp_Forget G) :
  `1 (fg_ker_idx h) = fg_ker h := eq_refl.

Example p442_ker_is_extension_kernel (G : Grp)
  (h : X ~{Sets}~> Grp_Forget G) (u v : FGWord X) :
  fg_ker h u v
    = @pequiv _ _ (grp_prop G) (fg_ev h u) (fg_ev h v) := eq_refl.

End PropSolutionReadbacks.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p442_sol_prop_is_not_singleton (X : Sets) :
  sol_index (Grp_Forget_solution_set_prop X) = poly_unit := eq_refl.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p442_two_applications_differ :
  free_group_via_GAFT = free_group_via_GAFT_from_adjunction := eq_refl.

(* * ** The payoff: 定理 applied at named sets

 Before PR these lines exhibited free group obtained an
 伴随 had been assumed order obtain it. （已译） *)

Check (Grp_Forget_solution_set_prop SetOne).
Check (Grp_Forget_solution_set_prop TwoLetters).
Check (FGCongIdx SetOne).
Check (FGCongIdx TwoLetters).
Check (`1 free_group_via_GAFT SetOne).
Check (fg_ker_idx (fg_insert TwoLetters)).
Check (fg_ker_med (fg_insert TwoLetters)).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetCarrierPin.

Universes pcar pobj.
Constraint pcar = Set.

Context (Xs : obj[Sets@{pcar pobj}]).

(* 相关说明。 （已译） *)
Definition p442_prop_sols_at_set_carrier : SolutionSet Grp_Forget Xs :=
  Grp_Forget_solution_set_prop Xs.

(* 相关说明。 （已译） *)
Definition p442_circular_app_at_set_carrier : obj[Grp] :=
  `1 free_group_via_GAFT_from_adjunction Xs.

(* 相关说明。 （已译） *)
Fail Definition p442_uncond_app_at_set_carrier : obj[Grp] :=
  `1 free_group_via_GAFT Xs.

End SetCarrierPin.

(*
   本节说明 ProbeGrpFreeAFT442 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (`1 free_group_via_GAFT_from_adjunction TwoLetters).

Fail Definition p442_uncond_at_two_letters : obj[Grp] :=
  `1 free_group_via_GAFT TwoLetters.
