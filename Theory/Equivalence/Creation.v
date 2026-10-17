Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(** * Equivalences create limits, and right adjoints preserve cones *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/adjoint+functor#preservation

   本文件给出极限/余极限的创造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Right adjoints preserve limiting cones, not merely limit apexes *)

Section EquivCreates.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(* An equivalence is (the left half of) an adjoint equivalence, hence a
   right adjoint, hence cone-level continuous. *)

Definition equivalence_PreservesLimitCone {J : Category} (K : J ⟶ C) :
  PreservesLimitCone K F :=
  right_adjoint_PreservesLimitCone
    (AdjointEquivalence_swap_adjunction (Equivalence_to_AdjointEquivalence E)) K.

(*
   本节说明函子、（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition equivalence_ReflectsLimitCone {J : Category} (K : J ⟶ C) :
  ReflectsLimitCone K F :=
  fun M H =>
    @ff_ReflectsLimitCone C D F (Equivalence_Full E) (Equivalence_Faithful E)
      J K M H.

(* The naming defect of [equivalence_creates_limits], resolved by proof:
   that constant supplies the lift, and the two remaining clauses are the
   two lemmas above. *)

Definition equivalence_CreatesLimit {J : Category} (K : J ⟶ C) :
  CreatesLimit K F.
Proof using E.
  unshelve refine
    {| creates_lift := fun N HN =>
         @limit_cone _ _ _
           (equivalence_creates_limits E K (@Build_Limit J D (F ◯ K) N HN)) |}.
  - intros N HN.
    exact (limitcone_iso
             (equivalence_PreservesLimitCone K _ (limit_limitcone _)) HN).
  - exact (equivalence_ReflectsLimitCone K).
Defined.

Definition equivalence_CreatesAllLimits : CreatesAllLimits F :=
  fun J K => equivalence_CreatesLimit K.

End EquivCreates.

(** ** The identity functor creates every limit *)

Definition Id_CreatesAllLimits {C : Category} : CreatesAllLimits Id[C] :=
  equivalence_CreatesAllLimits (@EquivalenceOfCategories_Id C).
