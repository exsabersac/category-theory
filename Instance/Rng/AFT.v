Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(* * * The free ring 函子, read through adjoint 函子 定理 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/free+ring
 nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* On data these two 函子 same term. The records not
 convertible -- see header -- why two recones below
 exist at all. （已译） *)

Example rng_forget_factors_obj (R : Rng) :
  fobj[Rng_Forget] R = fobj[Ab_Forget ◯ Rng_Forget_Ab] R := eq_refl.

Example rng_forget_factors_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[Rng_Forget] f = fmap[Ab_Forget ◯ Rng_Forget_Ab] f := eq_refl.

(* [RngUnderlyingAb] (Instance/Rng/Free.v) IS 复合, so the
 same two readbacks hold against it. These what make retyping of
 [free_ring_via_ab_adjunction] typecheck. （已译） *)

Example rng_underlying_ab_is_forget_obj (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[Rng_Forget] R := eq_refl.

Example rng_underlying_ab_is_forget_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[Rng_Forget] f := eq_refl.

(* * * Continuity [Rng_Forget_Ab], without creation 论元 FOR IT,
 without RAPL （已译） *)

Section RngAbContinuity.

Context {J : Category}.
Context (K : J ⟶ Rng).

(*
   本节说明 AFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rng_ab_recone (M : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)))
  : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Rng_Forget ◯ K)
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(* 相关说明。 （已译） *)
Definition rng_sets_recone (M : Cone (Rng_Forget ◯ K))
  : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) :=
  @Build_Cone J Sets (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rng_ab_image_limit (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Ab_Forget (FCone Rng_Forget_Ab N)) :=
  fun M => Rng_Forget_continuous J K N HN (rng_ab_recone M).

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rng_ab_limit_cone (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Rng_Forget_Ab N) :=
  Ab_Forget_reflects_limits (Rng_Forget_Ab ◯ K) (FCone Rng_Forget_Ab N)
    (rng_ab_image_limit N HN).

(* The same composite read backwards: [Ab_Forget] is continuous by
 creation ([Ab_Forget_creates_continuous], Instance/Ab/Limit.v, which
 presupposes no 伴随 either), [Rng_Forget] reflects.（已译） *)
Definition rng_ab_reflect (N : Cone K)
  (HN : IsLimitCone (FCone Rng_Forget_Ab N)) : IsLimitCone N :=
  Rng_Forget_reflects_limits K N
    (fun M =>
       Ab_Forget_creates_continuous J (Rng_Forget_Ab ◯ K)
         (FCone Rng_Forget_Ab N) HN (rng_sets_recone M)).

End RngAbContinuity.

(** The headline non-circular result. *)
Definition Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab :=
  fun J K N HN => rng_ab_limit_cone K N HN.

Definition Rng_Forget_Ab_PreservesAllLimits :
  PreservesAllLimits Rng_Forget_Ab :=
  Continuous_PreservesAllLimits Rng_Forget_Ab_continuous.

Definition Rng_Forget_Ab_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget_Ab :=
  fun N HN => rng_ab_reflect K N HN.

(* * * The underlying-set 伴随, retyped onto [Rng_Forget] （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_ab Rng_Forget
    (@adj _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction).

(* The 幺半群 route retyped same way, so comparison below can
 made against BOTH explicit constructions rather than one. （已译） *)
Definition free_ring_via_mon_adjunction_set : free_ring_via_mon ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_mon Rng_Forget
    (@adj _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab).

(* 相关说明。 （已译） *)
Example free_ring_via_ab_adjunction_set_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction_set X R) f
    = to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 AFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RngCongruence.

Context (A : AbObject).

Record IsRngCongruence (Rq : FRTerm A → FRTerm A → Prop) : Prop := {
  rc_refl  : ∀ s, Rq s s;
  rc_sym   : ∀ s t, Rq s t → Rq t s;
  rc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  rc_gen   : ∀ s t, fr_eq s t → Rq s t;
  rc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_plus A s t) (@fr_plus A s' t');
  rc_neg   : ∀ s s', Rq s s' → Rq (@fr_neg A s) (@fr_neg A s');
  rc_mul   : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_mul A s t) (@fr_mul A s' t')
}.

Definition RngCongIdx : Type :=
  { Rq : FRTerm A → FRTerm A → Prop & IsRngCongruence Rq }.

(*
   本节说明 AFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QRng_Setoid (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : Setoid (FRTerm A) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := rc_refl  Rq H
        ; Equivalence_Symmetric  := rc_sym   Rq H
        ; Equivalence_Transitive := rc_trans Rq H |} |}.

(* 相关说明。 （已译） *)
Definition QRng (Rq : FRTerm A → FRTerm A → Prop) (H : IsRngCongruence Rq)
  : RingObject :=
  {| ring_rig := {|
       rig_setoid :=
         {| carrier := FRTerm A
          ; is_setoid := QRng_Setoid Rq H |};
       rig_zero := @fr_zero A;
       rig_add  := @fr_plus A;
       rig_one  := @fr_one A;
       rig_mul  := @fr_mul A;
       rig_add_respects := fun _ _ Hs _ _ Ht => rc_plus Rq H _ _ _ _ Hs Ht;
       rig_mul_respects := fun _ _ Hs _ _ Ht => rc_mul Rq H _ _ _ _ Hs Ht;
       rig_add_assoc := fun s t u => rc_gen Rq H _ _ (fre_add_assoc s t u);
       rig_add_comm := fun s t => rc_gen Rq H _ _ (fre_add_comm s t);
       rig_add_zero_l := fun s => rc_gen Rq H _ _ (fre_add_zero_l s);
       rig_mul_assoc := fun s t u => rc_gen Rq H _ _ (fre_mul_assoc s t u);
       rig_mul_one_l := fun s => rc_gen Rq H _ _ (fre_mul_one_l s);
       rig_mul_one_r := fun s => rc_gen Rq H _ _ (fre_mul_one_r s);
       rig_distr_l := fun s t u => rc_gen Rq H _ _ (fre_distr_l s t u);
       rig_distr_r := fun s t u => rc_gen Rq H _ _ (fre_distr_r s t u);
       rig_mul_zero_l := fun s => rc_gen Rq H _ _ (fr_mul_zero_l A s);
       rig_mul_zero_r := fun s => rc_gen Rq H _ _ (fr_mul_zero_r A s);
       rig_prop := @PropEquiv_of_relation _ (QRng_Setoid Rq H) Rq
                     (fun _ _ h => h) (fun _ _ h => h)
     |};
     ring_neg := @fr_neg A;
     ring_neg_respects := fun _ _ Hs => rc_neg Rq H _ _ Hs;
     ring_neg_l := fun s => rc_gen Rq H _ _ (fre_neg_l s)
  |}.

(* The canonical 嵌入 [A] 进入 quotient. （已译） *)
Definition QRng_insert (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : A ~{Ab}~> Rng_Forget_Ab (QRng Rq H).
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := @fr_gen A |}.
    intros a b Hab; exact (rc_gen Rq H _ _ (fre_gen Hab)).
  - exact (rc_gen Rq H _ _ (@fre_gen_zero A)).
  - intros a b; exact (rc_gen Rq H _ _ (fre_gen_plus a b)).
Defined.

End RngCongruence.

Arguments IsRngCongruence {A} Rq.
Arguments RngCongIdx A.
Arguments QRng_Setoid {A} Rq H.
Arguments QRng {A} Rq H.
Arguments QRng_insert {A} Rq H.

(* 相关说明。 （已译） *)

Section RngKernel.

Context (A : AbObject).
Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Definition rng_ker : FRTerm A → FRTerm A → Prop :=
  fun s t => @pequiv _ _ (rig_prop R) (fr_eval h s) (fr_eval h t).

Lemma rng_ker_is_cong : IsRngCongruence rng_ker.
Proof.
  unfold rng_ker.
  constructor.
  - intro s; apply (@pequiv_from _ _ (rig_prop R)); reflexivity.
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R)); symmetry;
      exact (@pequiv_to _ _ (rig_prop R) _ _ Hst).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (rig_prop R)).
    transitivity (fr_eval h t);
      [ exact (@pequiv_to _ _ (rig_prop R) _ _ H1)
      | exact (@pequiv_to _ _ (rig_prop R) _ _ H2) ].
  (* [fr_eval_respects] takes [R] EXPLICITLY (Instance/Rng/Free.v)
     while [fr_eval] takes both implicitly. *)
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R));
      exact (fr_eval_respects R h s t Hst).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_add_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
  - intros s s' H1; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (ring_neg_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_mul_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
Qed.

Definition rng_ker_idx : RngCongIdx A := existT _ rng_ker rng_ker_is_cong.

(* 相关说明。 （已译） *)
Program Definition rng_ker_med : QRng rng_ker rng_ker_is_cong ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval h |}
|}.
Solve All Obligations with
  (first [ (intros s t Hst; exact (@pequiv_to _ _ (rig_prop R) _ _ Hst))
         | (intros; simpl; reflexivity) ]).

(* 相关说明。 （已译） *)
Example rng_ker_factors (a : carrier (cmon_setoid A)) :
  rig_map rng_ker_med (cmon_map (QRng_insert rng_ker rng_ker_is_cong) a)
  = cmon_map h a
  := eq_refl.

End RngKernel.

Arguments rng_ker {A R} h.
Arguments rng_ker_is_cong {A R} h.
Arguments rng_ker_idx {A R} h.
Arguments rng_ker_med {A R} h.

(* 相关说明。 （已译） *)
Definition QRngOf {A : Ab} (i : RngCongIdx A) : obj[Rng] :=
  QRng (`1 i) (`2 i).

Definition QRngInsertOf {A : Ab} (i : RngCongIdx A)
  : A ~{Ab}~> Rng_Forget_Ab (QRngOf i) := QRng_insert (`1 i) (`2 i).

Definition Rng_Forget_Ab_solution_set_prop (A : Ab) :
  SolutionSet Rng_Forget_Ab A.
Proof.
  unshelve refine (@Build_SolutionSet Rng Ab Rng_Forget_Ab A
                     (RngCongIdx A) QRngOf QRngInsertOf _).
  intros c h.
  exists (rng_ker_idx h), (rng_ker_med h).
  intro a; simpl; reflexivity.
Defined.

(*
   本节说明 AFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Rng_Forget_solution_set_prop (X : Sets) :
  SolutionSet Rng_Forget X.
Proof.
  unshelve refine (@Build_SolutionSet Rng Sets Rng_Forget X
                     (RngCongIdx (FreeAbObject X)) QRngOf
                     (fun i => fmap[Ab_Forget] (QRngInsertOf i)
                                 ∘ free_ab_unit X) _).
  intros c h.
  exists (rng_ker_idx (@free_ab_extend X (Rng_Forget_Ab c) h)),
         (rng_ker_med (@free_ab_extend X (Rng_Forget_Ab c) h)).
  intro a; simpl.
  reflexivity.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Rng_Forget_Ab_solution_set_from_adjunction (A : Ab) :
  SolutionSet Rng_Forget_Ab A :=
  solution_set_of_adjunction free_rng_ab_adjunction A.

Definition Rng_Forget_solution_set_from_adjunction (X : Sets) :
  SolutionSet Rng_Forget X :=
  solution_set_of_adjunction free_ring_via_ab_adjunction_set X.

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_rng_ab_via_GAFT : ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_prop.

(* Second half: the free ring on a set, likewise non-circular. *)
Definition free_ring_via_GAFT : ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_prop.

(* 相关说明。 （已译） *)
Definition free_rng_ab_via_GAFT_from_adjunction :
  ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_from_adjunction.

Definition free_ring_via_GAFT_from_adjunction :
  ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_from_adjunction.

(** * The comparison clauses, at [≈] *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_rng_ab_via_GAFT_agrees : `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoints_agree (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction.

Definition free_ring_via_GAFT_agrees :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoints_agree (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set.

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_ring_via_GAFT_agrees_mon :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoints_agree (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example free_rng_ab_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoint_iso Rng_Forget_Ab _ FreeRngAb (`2 free_rng_ab_via_GAFT)
    free_rng_ab_adjunction.

Example free_ring_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoint_iso Rng_Forget _ free_ring_via_ab (`2 free_ring_via_GAFT)
    free_ring_via_ab_adjunction_set.

Example free_ring_via_GAFT_agrees_mon_via_left_adjoint_iso :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoint_iso Rng_Forget _ free_ring_via_mon
    (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(* * ** The comparison 态射, named （已译） *)

Definition free_rng_ab_via_GAFT_comparison (A : Ab)
  : `1 free_rng_ab_via_GAFT A ~{Rng}~> FreeRngAb A :=
  adj_left_compare (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction A.

Definition free_ring_via_GAFT_comparison (X : Sets)
  : `1 free_ring_via_GAFT X ~{Rng}~> free_ring_via_ab X :=
  adj_left_compare (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set X.

Definition free_ring_via_GAFT_comparison_mon (X : Sets)
  : `1 free_ring_via_GAFT_from_adjunction X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set X.

(* [left_adjoints_agree] [Defined], so each comparison IS component
 corresponding natural 同构, [eq_refl] not an
 论元. （已译） *)

Example free_rng_ab_via_GAFT_comparison_is_component (A : Ab) :
  to (projT1 free_rng_ab_via_GAFT_agrees A)
    = free_rng_ab_via_GAFT_comparison A := eq_refl.

Example free_ring_via_GAFT_comparison_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees X)
    = free_ring_via_GAFT_comparison X := eq_refl.

Example free_ring_via_GAFT_comparison_mon_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees_mon X)
    = free_ring_via_GAFT_comparison_mon X := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem free_rng_ab_via_GAFT_unit (A : Ab) :
  fmap[Rng_Forget_Ab] (free_rng_ab_via_GAFT_comparison A)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_rng_ab_via_GAFT) A
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.
Proof.
  exact (adj_left_compare_unit (`2 free_rng_ab_via_GAFT)
           free_rng_ab_adjunction A).
Qed.

Theorem free_ring_via_GAFT_unit (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_ring_via_GAFT) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT)
           free_ring_via_ab_adjunction_set X).
Qed.

Theorem free_ring_via_GAFT_unit_mon (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison_mon X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        (`2 free_ring_via_GAFT_from_adjunction) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT_from_adjunction)
           free_ring_via_mon_adjunction_set X).
Qed.
