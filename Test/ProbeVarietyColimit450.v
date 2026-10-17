(*
   本文件为测试：ProbeVarietyColimit450。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Instance.Variety.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Variety.Spanning.
Require Import Category.Instance.Variety.Colimit.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe450_variety_absent_name.

(** ** A. The headlines at their stated types, and the route by [eq_refl] *)

Section Headlines.

Context {S : UA.OpSignature} (E : UA.EqSignature S).

Check (SVariety_Complete E : @Complete (SVariety E)).
Check (SVariety_Forget_continuous E : ContinuousFunctor (SVariety_Forget E)).
Check (SVariety_colim_via_GAFT E : ∀ J : Category,
  { L : [J, SVariety E] ⟶ SVariety E & L ⊣ @Diagonal (SVariety E) J }).
Check (SVariety_Cocomplete_via_GAFT E : @Cocomplete (SVariety E)).
Check (SVariety_Cocartesian_via_GAFT E : @Cocartesian (SVariety E)).
Check (SVariety_coequalizers_via_GAFT E : HasCoequalizers (SVariety E)).
Check (SVariety_Initial_via_GAFT E : @Initial (SVariety E)).
Check (SVariety_Terminal E : @Terminal (SVariety E)).
Check (SVariety_Initial E : @Initial (SVariety E)).
Check (Free_Variety_via_GAFT E :
  { F : Sets ⟶ SVariety E & F ⊣ SVariety_Forget E }).

Example p450v_colim_is_GAFT (J : Category) :
  SVariety_colim_via_GAFT E J
    = GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
           (Continuous_PreservesImageLimit Diagonal_continuous)
           (@Diagonal_SVariety_solution_set S E J) := eq_refl.

(* The index IS the type of cocone congruences on the term algebra. *)
Example p450v_index (J : Category) (D : J ⟶ SVariety E) :
  sol_index (Diagonal_SVariety_solution_set E D) = VCongIdx E D := eq_refl.

Example p450v_member (J : Category) (D : J ⟶ SVariety E)
  (i : VCongIdx E D) :
  sol_obj (Diagonal_SVariety_solution_set E D) i = VQ_alg E D i := eq_refl.

(* Exercise 4's coequalizers are Structure/Limit/Finite.v's bridges over
   the AFT colimits. *)
Example p450v_coequalizers_bridge :
  SVariety_coequalizers_via_GAFT E
    = HasCoequalizers_of_HasEqualizers_op
        (FinitelyComplete_HasEqualizers
           (FinitelyCocomplete_FinitelyComplete_op
              (Cocomplete_FinitelyCocomplete
                 (SVariety_Cocomplete_via_GAFT E)))) := eq_refl.

(* Mac Lane's own route to the free algebra, at the congruence index. *)
Example p450v_free_is_GAFT :
  Free_Variety_via_GAFT E
    = GAFT (SVariety_Forget E) (SVariety_Complete E)
           (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
           (SVariety_Forget_solution_set E) := eq_refl.

Example p450v_free_index (X : Sets) :
  sol_index (SVariety_Forget_solution_set E X) = FCongIdx E X := eq_refl.

(** ** N1 (CONVERSION): the AFT initial object's carrier does not reduce *)

(* CONTROL: the initial algebra IS the free algebra on the empty set... *)
Example p450v_initial_is_free :
  @initial_obj (SVariety E) (SVariety_Initial E)
    = Free_Variety E (@initial_obj Sets _) := eq_refl.

(* CONTROL: ...and its carrier IS the closed terms. *)
Example p450v_initial_carrier :
  carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
    = UA.Tree S False := eq_refl.

(* CONTROL: the two initial objects agree, as data. *)
Check (SVariety_Initial_agrees E :
  @initial_obj (SVariety E) (SVariety_Initial E)
    ≅ @initial_obj (SVariety E) (SVariety_Initial_via_GAFT E)).

Fail Example p450v_n1_aft_initial_carrier :
  carrier (soa_obj (`1 (@initial_obj (SVariety E)
                                     (SVariety_Initial_via_GAFT E))))
    = UA.Tree S False := eq_refl.

(** ** N2 (CONVERSION): the free algebra from [GAFT] is `≈`, no more *)

(* CONTROL: the agreement that holds. *)
Check (Free_Variety_via_GAFT_agrees E :
  projT1 (Free_Variety_via_GAFT E) ≈ Free_Variety_Functor E).

Fail Example p450v_n2_aft_free_is_free :
  projT1 (Free_Variety_via_GAFT E) = Free_Variety_Functor E := eq_refl.

(** ** IX.1 Exercise 2: emptiness, and the category is never empty *)

Check (SVariety_initial_empty_iff E :
  (carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
     → False) ↔
  ({ o : UA.operation S & UA.arity o → False } → False)).
Check (closed_terms_empty_iff S :
  (UA.Tree S False → False) ↔
  (∀ o : UA.operation S, (UA.arity o → False) → False)).
Check (@dec_closed_term_constant S :
  (∀ o : UA.operation S, (UA.arity o → False) + UA.arity o) →
  UA.Tree S False → { o : UA.operation S & UA.arity o → False }).

End Headlines.

Check (closed_term_constant_implies_WLEM :
  (∀ S : UA.OpSignature,
     UA.Tree S False → { o : UA.operation S & UA.arity o → False }) →
  ∀ P : Prop, (P → False) + ((P → False) → False)).
Check (leibniz_coequalizers_iff_quotients :
  HasCoequalizers (Variety NoEq) ↔ QuotElim).

(* Non-vacuity at a presentation built without extensionality. *)
Check (CommMagma_Cocartesian : @Cocartesian (SVariety CommEq)).
Check (CommMagma_coequalizers : HasCoequalizers (SVariety CommEq)).

(*
   本节说明 ProbeVarietyColimit450 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* CONTROLS: discrete two-object shapes whose homs are free. *)
Definition p450v_colim_bool {S : UA.OpSignature} (E : UA.EqSignature S) :=
  SVariety_colim_via_GAFT E (DiscreteCat bool).
Definition p450v_colim_fin2 {S : UA.OpSignature} (E : UA.EqSignature S) :=
  SVariety_colim_via_GAFT E (DiscreteCat (Fin.t 2)).

Fail Definition p450v_n3_two_discrete {S : UA.OpSignature}
  (E : UA.EqSignature S) := SVariety_colim_via_GAFT E Two_Discrete.

(** ** N4 (UNIVERSE): at a [Set] carrier the solution set elaborates and
    [GAFT] does not *)

(* CONTROL: the diagonal solution set with the shape's homs, and hence the
   algebras' carrier, at [Set]. *)
Definition p450v_sols_at_set {S : UA.OpSignature} (E : UA.EqSignature S)
  (J : Category@{Set Set Set}) (D : J ⟶ SVariety E) :=
  Diagonal_SVariety_solution_set E D.

(* CONTROL: [GAFT] at the same diagonal with every argument but the
   solution set, so that neither completeness nor continuity is what a
   [Set] carrier refuses. *)
Definition p450v_gaft_partial_at_set {S : UA.OpSignature}
  (E : UA.EqSignature S) (J : Category@{Set Set Set}) :=
  GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
       (Continuous_PreservesImageLimit Diagonal_continuous).

Fail Definition p450v_n4_colim_at_set {S : UA.OpSignature}
  (E : UA.EqSignature S) (J : Category@{Set Set Set}) :=
  SVariety_colim_via_GAFT E J.

(** ** N5 (UNIVERSE): [GAFT] refuses the spanning solution set *)

(* CONTROL: the same call at the congruence-indexed family. *)
Definition p450v_gaft_congruences {S : UA.OpSignature}
  (E : UA.EqSignature S) :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (SVariety_Forget_solution_set E).

(* CONTROL: the spanning family itself elaborates. *)
Definition p450v_spanning {S : UA.OpSignature} (E : UA.EqSignature S) :=
  variety_solution_set E.

Fail Definition p450v_n5_gaft_spanning {S : UA.OpSignature}
  (E : UA.EqSignature S) :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (variety_solution_set E).

(** ** Guard block *)

Check @SVGen.
Check @IsVCong.
Check @VCongIdx.
Check @VQ_alg.
Check @vq_leg.
Check @vq_arr.
Check @vker.
Check @vker_cong.
Check @vker_idx.
Check @vker_med.
Check @Diagonal_SVariety_solution_set.
Check @IsFCong.
Check @FCongIdx.
Check @FQ_alg.
Check @fker_med.
Check @SVariety_Forget_solution_set.
Check @SVariety_Complete.
Check @SVariety_Forget_continuous.
Check @svariety_complete_carrier.
Check @WLEM_sig.
Check @WLEM_term.
Check @NoOp.
Check @NoEq.
Check @QuotElim.
Check @leibniz_coequalizers_give_quotients.
Check @quotients_give_leibniz_coequalizers.
Check @soa_prop.
Check @tree_equiv.
Check @variety_solution_set.
Check @Diagonal_continuous.
