Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.
Require Import Category.Construction.Lift.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Book:   Riehl, "Category Theory in Context", 2nd ed., §3.4, Exercise
   Paper:  Paré, "On absolute colimits", J. Algebra 19 (1971) 80-95
   nLab:   https://ncatlab.org/nlab/show/absolute+colimit
   nLab:   https://ncatlab.org/nlab/show/preserved+limit

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The two predicates *)

Definition AbsoluteLimitCone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) : Type :=
  ∀ (D : Category@{do ch ch}) (F : C ⟶ D), IsLimitCone (FCone F N).

Definition AbsoluteColimitCocone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cocone K) : Type :=
  ∀ (D : Category@{do ch ch}) (F : C ⟶ D), IsColimitCocone (FCocone F N).

(** ** An absolute limit is a limit *)

(* 相关说明。 （已译） *)

Example FCone_Id_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) : vertex_obj[FCone Id N] = vertex_obj[N] := eq_refl.

Example FCone_Id_leg@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (N : Cone K) (x : J) : cone_leg (FCone Id N) x = cone_leg N x := eq_refl.

(* 相关说明。 （已译） *)

Definition AbsoluteLimitCone_IsLimitCone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone N) : IsLimitCone N :=
  fun M => A C Id (cone_id_comp M).

(* 相关说明。 （已译） *)

Definition AbsoluteColimitCocone_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  @AbsoluteLimitCone (J^op) (C^op) (K^op) N :=
  fun D F M =>
    A (D^op)%category (F^op)%functor
      (@cone_op_comp_inv J C (D^op)%category K (F^op)%functor M).

Definition AbsoluteColimitCocone_of_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone N :=
  fun D F M => A (D^op)%category (F^op)%functor (cone_op_comp M).

Example AbsoluteColimitCocone_of_op_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone_of_op (AbsoluteColimitCocone_op A) = A := eq_refl.

Example AbsoluteColimitCocone_op_of_op@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone_op (AbsoluteColimitCocone_of_op A) = A := eq_refl.

Definition AbsoluteColimitCocone_IsColimitCocone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) : IsColimitCocone N :=
  AbsoluteLimitCone_IsLimitCone (AbsoluteColimitCocone_op A).

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AbsoluteLimitCone_IsLimitCone_up@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N) :
  IsLimitCone N.
Proof.
  intro M.
  pose (Ml := @Build_Cone J (LiftCat C) (Lift_in C ◯ K)
                (@vertex_obj _ _ _ M)
                (@Build_ACone J (LiftCat C) (@vertex_obj _ _ _ M)
                   (Lift_in C ◯ K)
                   (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
                   (fun x y f =>
                      @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f))).
  pose (U := A (LiftCat C) (Lift_in C) Ml).
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - intro x. exact (unique_property U x).
  - intros v Hv. exact (uniqueness U v Hv).
Defined.

Definition AbsoluteColimitCocone_IsColimitCocone_up@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone@{jo co ch do _ _ _ _} N) :
  IsColimitCocone N :=
  AbsoluteLimitCone_IsLimitCone_up (AbsoluteColimitCocone_op A).

(* Each instance implies every lower one: target D at level below the
 假设' read at level, [Lift_after F] replaces F. （已译） *)

Definition AbsoluteLimitCone_down@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone@{jo co ch eo _ _ _ _} N) :
  AbsoluteLimitCone@{jo co ch do _ _ _ _} N.
Proof.
  intros D F M.
  pose (Ml := @Build_Cone J (LiftCat D) (Lift_after F ◯ K)
                (@vertex_obj _ _ _ M)
                (@Build_ACone J (LiftCat D) (@vertex_obj _ _ _ M)
                   (Lift_after F ◯ K)
                   (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
                   (fun x y f =>
                      @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f))).
  pose (U := A (LiftCat D) (Lift_after F) Ml).
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - intro x. exact (unique_property U x).
  - intros v Hv. exact (uniqueness U v Hv).
Defined.

Definition AbsoluteColimitCocone_down@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone@{jo co ch eo _ _ _ _} N) :
  AbsoluteColimitCocone@{jo co ch do _ _ _ _} N :=
  AbsoluteColimitCocone_of_op
    (AbsoluteLimitCone_down (AbsoluteColimitCocone_op A)).

(* * ** Absoluteness preservation every 函子 （已译） *)

Definition AbsoluteLimitCone_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (HN : IsLimitCone N) (A : AbsoluteLimitCone N)
  (D : Category@{do ch ch}) (F : C ⟶ D) : PreservesLimitCone K F :=
  PreservesLimitCone_of_cone F N HN (A D F).

Definition AbsoluteLimitCone_of_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (HN : IsLimitCone N)
  (P : ∀ (D : Category@{do ch ch}) (F : C ⟶ D), PreservesLimitCone K F) :
  AbsoluteLimitCone N :=
  fun D F => P D F N HN.

Definition AbsoluteColimitCocone_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (HN : IsColimitCocone N) (A : AbsoluteColimitCocone N)
  (D : Category@{do ch ch}) (F : C ⟶ D) : PreservesColimitCocone K F :=
  PreservesColimitCocone_of_cocone F N HN (A D F).

Definition AbsoluteColimitCocone_of_preserves@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (HN : IsColimitCocone N)
  (P : ∀ (D : Category@{do ch ch}) (F : C ⟶ D),
         PreservesColimitCocone K F) :
  AbsoluteColimitCocone N :=
  fun D F => P D F N HN.

(* 相关说明。 （已译） *)

Definition AbsoluteLimitCone_transport@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cone K} (i : ConeIso N M) (A : AbsoluteLimitCone N) :
  AbsoluteLimitCone M :=
  fun D F => limitcone_transport (FCone_iso F i) (A D F).

Definition AbsoluteColimitCocone_transport@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cocone K} (i : ConeIso N M) (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone M :=
  AbsoluteColimitCocone_of_op
    (AbsoluteLimitCone_transport i (AbsoluteColimitCocone_op A)).

(* 相关说明。 （已译） *)

Definition AbsoluteLimitCone_limitcone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cone K} (HN : IsLimitCone N) (HM : IsLimitCone M)
  (A : AbsoluteLimitCone N) : AbsoluteLimitCone M :=
  AbsoluteLimitCone_transport (limitcone_iso HN HM) A.

Definition AbsoluteColimitCocone_colimitcocone@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N M : Cocone K} (HN : IsColimitCocone N) (HM : IsColimitCocone M)
  (A : AbsoluteColimitCocone N) : AbsoluteColimitCocone M :=
  AbsoluteColimitCocone_transport (colimitcocone_iso HN HM) A.

(* * ** Closure under 函子: image absolute limit absolute （已译） *)

Definition AbsoluteLimitCone_image@{jo co ch eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {E : Category@{eo ch ch}} {K : J ⟶ C} {N : Cone K}
  (A : AbsoluteLimitCone N) (G : C ⟶ E) : AbsoluteLimitCone (FCone G N) :=
  fun D H => islimitcone_assoc (A D (H ◯ G)).

Definition AbsoluteColimitCocone_image@{jo co ch eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {E : Category@{eo ch ch}} {K : J ⟶ C} {N : Cocone K}
  (A : AbsoluteColimitCocone N) (G : C ⟶ E) :
  AbsoluteColimitCocone (FCocone G N) :=
  fun D H M => A D (H ◯ G) (cocone_assoc_inv M).

(* 相关说明。 （已译） *)


(* 相关说明。 （已译） *)

Definition empty_shape_cone {C : Category} (G : _0 ⟶ C) (c : C) : Cone G.
Proof.
  unshelve refine (@Build_Cone _0 C G c _).
  unshelve econstructor; intro x; destruct x.
Defined.

Definition empty_shape_cocone {C : Category} (G : _0 ⟶ C) (c : C) :
  Cocone G.
Proof.
  unshelve refine (@Build_Cone (_0^op) (C^op) (G^op) c _).
  unshelve econstructor; intro x; destruct x.
Defined.

(* 相关说明。 （已译） *)

Definition two_into_TwoY (m : TwoObj) : TwoHom m TwoY :=
  match m with TwoX => TwoXY | TwoY => TwoIdY end.

Definition two_out_of_TwoX (m : TwoObj) : TwoHom TwoX m :=
  match m with TwoX => TwoIdX | TwoY => TwoXY end.

Definition two_terminal_IsLimitCone :
  IsLimitCone (empty_shape_cone (From_0 _2) (TwoY : _2)).
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (two_into_TwoY (@vertex_obj _ _ _ M)).
  - intro x; destruct x.
  - intros v _; apply Two_thin.
Defined.

Definition two_initial_IsColimitCocone :
  IsColimitCocone (empty_shape_cocone (From_0 _2) (TwoX : _2)).
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (two_out_of_TwoX (@vertex_obj _ _ _ M)).
  - intro x; destruct x.
  - intros v _; apply Two_thin.
Defined.

(* The 常值 函子 at [TwoX] sends terminal [TwoY] [TwoX],
 receives no arrow [TwoY]; dually 常值 函子 at
 [TwoY] sends initial [TwoX] [TwoY]. （已译） *)

Theorem two_terminal_not_absolute :
  AbsoluteLimitCone (empty_shape_cone (From_0 _2) (TwoY : _2)) → False.
Proof.
  intro A.
  destruct (A _2 Δ[_2]((TwoX : _2))
              (empty_shape_cone (Δ[_2]((TwoX : _2)) ◯ From_0 _2)
                 (TwoY : _2)))
    as [u _ _].
  exact (TwoHom_Y_X_absurd u).
Qed.

Theorem two_initial_not_absolute :
  AbsoluteColimitCocone (empty_shape_cocone (From_0 _2) (TwoX : _2)) →
  False.
Proof.
  intro A.
  destruct (A _2 Δ[_2]((TwoY : _2))
              (empty_shape_cocone (Δ[_2]((TwoY : _2)) ◯ From_0 _2)
                 (TwoX : _2)))
    as [u _ _].
  exact (TwoHom_Y_X_absurd u).
Qed.
