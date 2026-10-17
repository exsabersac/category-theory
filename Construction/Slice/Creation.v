Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Set Universe Polymorphism.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出极限/余极限的创造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The 恒等 own 右伴随, so comma side free （已译） *)

Definition Id_PreservesImageLimit {C : Category} : @PreservesImageLimit C C Id
  := right_adjoint_PreservesImageLimit (@Adjunction_Id C).

Section CosliceComma.

Context {C : Category}.
Context (c : C).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coslice_comma_StrictlyCreatesLimit
  {J : Category} (K : J ⟶ (=(c) ↓ Id)) :
  StrictlyCreatesLimit K comma_proj2 :=
  comma_StrictlyCreatesLimit K
    (fun N HN => Id_PreservesImageLimit J (Gdiag K)
                   (@Build_Limit J C (Gdiag K) N HN)).

Definition coslice_comma_CreatesAllLimits :
  CreatesAllLimits (@comma_proj2 _ _ _ (=(c)) (Id[C])) :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (coslice_comma_StrictlyCreatesLimit K).

(* Completeness of the coslice-as-comma, obtained THROUGH creation rather
   than through [Comma_Complete]. *)

Definition coslice_comma_Complete (HC : @Complete C) : @Complete (=(c) ↓ Id) :=
  creates_limits_Complete comma_proj2 HC coslice_comma_CreatesAllLimits.

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coslice_comma_Complete_via_adjoint (HC : @Complete C) :
  @Complete (=(c) ↓ Id) :=
  Comma_Complete_right_adjoint (@Adjunction_Id C) c HC.

(* 相关说明。 （已译） *)

Definition Coslice_to_Comma : (c ̸co C) ⟶ (=(c) ↓ Id) :=
  to (Comma_Coslice C c).

Definition Coslice_Comma_Equivalence :
  @EquivalenceOfCategories (c ̸co C) (=(c) ↓ Id) Coslice_to_Comma :=
  Cat_Iso_to_Equivalence (Comma_Coslice C c).

Definition Coslice_to_Comma_CreatesAllLimits :
  CreatesAllLimits Coslice_to_Comma :=
  equivalence_CreatesAllLimits Coslice_Comma_Equivalence.

Definition Coslice_Complete (HC : @Complete C) : @Complete (c ̸co C) :=
  creates_limits_Complete Coslice_to_Comma (coslice_comma_Complete HC)
    Coslice_to_Comma_CreatesAllLimits.

(* 相关说明。 （已译） *)

Definition coslice_comma_proj : (c ̸co C) ⟶ C := comma_proj2 ◯ Coslice_to_Comma.

Definition coslice_comma_proj_CreatesLimit {J : Category} (K : J ⟶ (c ̸co C)) :
  CreatesLimit K coslice_comma_proj :=
  CreatesLimit_compose (Coslice_to_Comma_CreatesAllLimits J K)
    (coslice_comma_CreatesAllLimits J (Coslice_to_Comma ◯ K)).

Definition coslice_comma_proj_CreatesAllLimits :
  CreatesAllLimits coslice_comma_proj :=
  fun J K => coslice_comma_proj_CreatesLimit K.

End CosliceComma.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CosliceCreate.

Context {C : Category}.
Context (c : C).
Context {J : Category}.
Context (K : J ⟶ (c ̸co C)).

Lemma coslice_structure_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Coslice_Proj c ◯ K] f ∘ `2 (K x) ≈ `2 (K y).
Proof.
  symmetry.
  exact (`2 (fmap[K] f)).
Qed.

Definition coslice_structure_cone : Cone (Coslice_Proj c ◯ K) :=
  @Build_Cone J C (Coslice_Proj c ◯ K) c
    (@Build_ACone J C c (Coslice_Proj c ◯ K)
       (fun j => `2 (K j)) (@coslice_structure_coherence)).

(* 相关说明。 （已译） *)

Definition coslice_reflect_at (M : Cone K)
  (HM : IsLimitCone (FCone (Coslice_Proj c) M)) : IsLimitCone M.
Proof.
  intro N.
  destruct (HM (FCone (Coslice_Proj c) N)) as [w Hw Hwu].
  assert (Hsq : `2 (vertex_obj[M]) ≈ w ∘ `2 (vertex_obj[N])).
  { transitivity (unique_obj (HM coslice_structure_cone)).
    - symmetry.
      apply (uniqueness (HM coslice_structure_cone)).
      intro j.
      symmetry.
      exact (`2 (cone_leg M j)).
    - apply (uniqueness (HM coslice_structure_cone)).
      intro j.
      rewrite comp_assoc.
      rewrite (Hw j).
      symmetry.
      exact (`2 (cone_leg N j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j.
    exact (Hw j).
  - intros v Hv.
    apply Hwu.
    intro j.
    exact (Hv j).
Defined.

Section CosliceLift.

Context (N : Cone (Coslice_Proj c ◯ K)).
Context (HN : IsLimitCone N).

Definition coslice_med : c ~{C}~> vertex_obj[N] :=
  unique_obj (HN coslice_structure_cone).

Lemma coslice_med_commutes (j : J) :
  cone_leg N j ∘ coslice_med ≈ `2 (K j).
Proof.
  exact (unique_property (HN coslice_structure_cone) j).
Qed.

Definition coslice_lift_obj : c ̸co C := (vertex_obj[N]; coslice_med).

Definition coslice_lift_leg (j : J) : coslice_lift_obj ~{c ̸co C}~> K j.
Proof.
  unshelve refine (cone_leg N j; _).
  symmetry.
  exact (coslice_med_commutes j).
Defined.

Lemma coslice_lift_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ coslice_lift_leg x ≈ coslice_lift_leg y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
Qed.

Definition coslice_lift_cone : Cone K :=
  @Build_Cone J (c ̸co C) K coslice_lift_obj
    (@Build_ACone J (c ̸co C) coslice_lift_obj K
       coslice_lift_leg (@coslice_lift_coherence)).

Definition coslice_lift_ump (M : Cone K) :
  ∃! u : vertex_obj[M] ~{c ̸co C}~> coslice_lift_obj,
    ∀ j : J, coslice_lift_leg j ∘ u ≈ cone_leg M j.
Proof.
  destruct (HN (FCone (Coslice_Proj c) M)) as [w Hw Hwu].
  assert (Hsq : coslice_med ≈ w ∘ `2 (vertex_obj[M])).
  { unfold coslice_med.
    apply (uniqueness (HN coslice_structure_cone)).
    intro j.
    rewrite comp_assoc.
    rewrite (Hw j).
    symmetry.
    exact (`2 (cone_leg M j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j.
    exact (Hw j).
  - intros v Hv.
    apply Hwu.
    intro j.
    exact (Hv j).
Defined.

Definition coslice_limit_at : Limit K :=
  @Build_Limit J (c ̸co C) K coslice_lift_cone coslice_lift_ump.

(* 相关说明。 （已译） *)

Definition coslice_strict_lift : StrictLift K (Coslice_Proj c) N :=
  @Build_StrictLift J (c ̸co C) C K (Coslice_Proj c) N
    coslice_lift_cone eq_refl (fun x => reflexivity _).

Definition coslice_lift_apex :
  fobj[Coslice_Proj c] (vertex_obj[coslice_lift_cone]) = vertex_obj[N]
  := eq_refl.

Definition coslice_lift_legs (j : J) :
  fmap[Coslice_Proj c] (cone_leg coslice_lift_cone j) = cone_leg N j
  := eq_refl.

End CosliceLift.

Definition Coslice_Proj_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (Coslice_Proj c).
Proof.
  unshelve refine {| screates := coslice_strict_lift |}.
  - intros N HN.
    exact (limit_limitcone (coslice_limit_at N HN)).
  - exact coslice_reflect_at.
Defined.

Definition Coslice_Proj_CreatesLimit : CreatesLimit K (Coslice_Proj c) :=
  StrictlyCreatesLimit_CreatesLimit Coslice_Proj_StrictlyCreatesLimit.

End CosliceCreate.

Definition Coslice_Proj_CreatesAllLimits {C : Category} (c : C) :
  CreatesAllLimits (Coslice_Proj c) :=
  fun J K => Coslice_Proj_CreatesLimit c K.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Coslice_Complete_direct {C : Category} (c : C) (HC : @Complete C) :
  @Complete (c ̸co C) :=
  creates_limits_Complete (Coslice_Proj c) HC (Coslice_Proj_CreatesAllLimits c).
