Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* * * The arrow-范畴 projection creates limits （已译） *)

(*
   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The 恒等 函子 preserves limiting cones （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Id_PreservesLimitCone {J D : Category} (G : J ⟶ D) :
  PreservesLimitCone G Id[D].
Proof.
  intros N HN M.
  pose (M' := @Build_Cone J D G vertex_obj[M]
                (@Build_ACone J D vertex_obj[M] G (cone_leg M)
                   (fun x y f => cone_leg_coh M f))).
  destruct (HN M') as [u Hu Huniq].
  exists u.
  - intro j; exact (Hu j).
  - intros v Hv; apply Huniq; intro j; exact (Hv j).
Defined.

(* 相关说明。 （已译） *)

Section TwoSided.

Context {A B C : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.
Context {J : Category}.
Context (K : J ⟶ (S ↓ T)).
Context (HT : PreservesLimitCone (comma_proj2 ◯ K) T).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cod_leg (N : Cone (comma_proj ◯ K)) (j : J) :
  snd vertex_obj[N] ~{B}~> (comma_proj2 ◯ K) j := snd (cone_leg N j).

Lemma cod_coherence (N : Cone (comma_proj ◯ K)) {x y : J} (f : x ~{J}~> y) :
  fmap[comma_proj2 ◯ K] f ∘ cod_leg N x ≈ cod_leg N y.
Proof. exact (snd (cone_leg_coh N f)). Qed.

Definition cod_cone (N : Cone (comma_proj ◯ K)) : Cone (comma_proj2 ◯ K) :=
  @Build_Cone J B (comma_proj2 ◯ K) (snd vertex_obj[N])
    (@Build_ACone J B (snd vertex_obj[N]) (comma_proj2 ◯ K) (cod_leg N)
       (fun x y f => cod_coherence N f)).

(* 相关说明。 （已译） *)

Definition cod_limiting (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (cod_cone N).
Proof.
  intro M.
  pose (M' := @Build_Cone J B (Snd ◯ (comma_proj ◯ K)) vertex_obj[M]
                (@Build_ACone J B vertex_obj[M] (Snd ◯ (comma_proj ◯ K))
                   (cone_leg M) (fun x y f => cone_leg_coh M f))).
  destruct (Snd_PreservesLimitCone (comma_proj ◯ K) N HN M') as [u Hu Huniq].
  exists u.
  - intro j; exact (Hu j).
  - intros v Hv; apply Huniq; intro j; exact (Hv j).
Defined.

Definition tcod_limiting (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (FCone T (cod_cone N)) :=
  HT (cod_cone N) (cod_limiting N HN).

(* 相关说明。 （已译） *)

Definition dom_leg (N : Cone (comma_proj ◯ K)) (j : J) :
  S (fst vertex_obj[N]) ~{C}~> (T ◯ (comma_proj2 ◯ K)) j :=
  `2 (K j) ∘ fmap[S] (fst (cone_leg N j)).

Lemma dom_coherence (N : Cone (comma_proj ◯ K)) {x y : J} (f : x ~{J}~> y) :
  fmap[T ◯ (comma_proj2 ◯ K)] f ∘ dom_leg N x ≈ dom_leg N y.
Proof.
  unfold dom_leg.
  change (fmap[T] (snd `1 (fmap[K] f))
            ∘ (`2 (K x) ∘ fmap[S] (fst (cone_leg N x)))
            ≈ `2 (K y) ∘ fmap[S] (fst (cone_leg N y))).
  rewrite comp_assoc.
  rewrite <- (`2 (fmap[K] f)).
  rewrite <- comp_assoc, <- fmap_comp.
  now rewrite (fst (cone_leg_coh N f)).
Qed.

Definition dom_cone (N : Cone (comma_proj ◯ K)) :
  Cone (T ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J C (T ◯ (comma_proj2 ◯ K)) (S (fst vertex_obj[N]))
    (@Build_ACone J C (S (fst vertex_obj[N])) (T ◯ (comma_proj2 ◯ K))
       (dom_leg N) (fun x y f => dom_coherence N f)).

Section Lift.

Context (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N).

(* The comparison arrow: mediator [dom_cone N] 进入 preserved
 codomain limit. （已译） *)

Definition comma_lift_arrow :
  S (fst vertex_obj[N]) ~{C}~> T (snd vertex_obj[N]) :=
  unique_obj (tcod_limiting N HN (dom_cone N)).

Lemma comma_lift_arrow_commutes (j : J) :
  fmap[T] (snd (cone_leg N j)) ∘ comma_lift_arrow
    ≈ `2 (K j) ∘ fmap[S] (fst (cone_leg N j)).
Proof. exact (unique_property (tcod_limiting N HN (dom_cone N)) j). Qed.

(* Mac Lane's uniqueness clause: any arrow making every square commute is
   the comparison arrow. *)

Lemma comma_lift_arrow_unique
  (h : S (fst vertex_obj[N]) ~{C}~> T (snd vertex_obj[N])) :
  (∀ j : J, fmap[T] (snd (cone_leg N j)) ∘ h
              ≈ `2 (K j) ∘ fmap[S] (fst (cone_leg N j))) →
  comma_lift_arrow ≈ h.
Proof. intro Hh. exact (uniqueness (tcod_limiting N HN (dom_cone N)) h Hh). Qed.

Definition comma_lift_obj : S ↓ T := (vertex_obj[N]; comma_lift_arrow).

Definition comma_lift_leg (j : J) : comma_lift_obj ~{S ↓ T}~> K j :=
  (cone_leg N j; symmetry (comma_lift_arrow_commutes j)).

Lemma comma_lift_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ comma_lift_leg x ≈ comma_lift_leg y.
Proof. exact (cone_leg_coh N f). Qed.

Definition comma_lift_cone : Cone K :=
  @Build_Cone J (S ↓ T) K comma_lift_obj
    (@Build_ACone J (S ↓ T) comma_lift_obj K comma_lift_leg
       (fun x y f => comma_lift_coherence f)).

(* 相关说明。 （已译） *)

Example comma_lift_apex_strict :
  comma_proj vertex_obj[comma_lift_cone] = vertex_obj[N] := eq_refl.

Example comma_lift_leg_strict (j : J) :
  fmap[comma_proj] (cone_leg comma_lift_cone j) = cone_leg N j := eq_refl.

Definition comma_lift_StrictLift : StrictLift K comma_proj N :=
  @Build_StrictLift J (S ↓ T) (A ∏ B) K comma_proj N comma_lift_cone eq_refl
    (fun j => reflexivity _).

End Lift.

(* Reflection: cone over [K] whose projection limiting limiting.
 The mediator downstairs comma 态射 because legs the
 preserved codomain limit jointly monic. （已译） *)

Definition comma_proj_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj M)) : IsLimitCone M.
Proof using HT.
  intro M'.
  destruct (HM (FCone comma_proj M')) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ fmap[S] (fst w)
                  ≈ fmap[T] (snd w) ∘ (`2 vertex_obj[M'])).
  { apply (limit_med_eq
             (limitcone_isalimit (tcod_limiting (FCone comma_proj M) HM))
             (dom_cone (FCone comma_proj M'))).
    - intro j.
      change (fmap[T] (snd `1 (cone_leg M j))
                ∘ ((`2 vertex_obj[M]) ∘ fmap[S] (fst w))
                ≈ (`2 (K j)) ∘ fmap[S] (fst `1 (cone_leg M' j))).
      rewrite comp_assoc.
      rewrite <- (`2 (cone_leg M j)).
      rewrite <- comp_assoc, <- fmap_comp.
      now rewrite (fst (Hw j)).
    - intro j.
      change (fmap[T] (snd `1 (cone_leg M j))
                ∘ (fmap[T] (snd w) ∘ (`2 vertex_obj[M']))
                ≈ (`2 (K j)) ∘ fmap[S] (fst `1 (cone_leg M' j))).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (snd (Hw j)).
      symmetry.
      exact (`2 (cone_leg M' j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j. exact (Hw j).
  - intros v Hv. apply Hwu. intro j. exact (Hv j).
Defined.

Definition comma_proj_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj.
Proof using HT.
  unshelve refine {| screates := fun N HN => comma_lift_StrictLift N HN |}.
  - intros N HN.
    apply comma_proj_reflect.
    exact (limitcone_transport
             (ConeIso_sym (slift_iso (comma_lift_StrictLift N HN);
                           slift_iso_legs (comma_lift_StrictLift N HN))) HN).
  - exact comma_proj_reflect.
Defined.

Definition comma_proj_CreatesLimit : CreatesLimit K comma_proj :=
  StrictlyCreatesLimit_CreatesLimit comma_proj_StrictlyCreatesLimit.

Definition comma_proj_Limit (L : Limit (comma_proj ◯ K)) : Limit K :=
  creates_limit_lift comma_proj_CreatesLimit L.

Example comma_proj_Limit_apex (L : Limit (comma_proj ◯ K)) :
  (`1 vertex_obj[comma_proj_Limit L]) = vertex_obj[L] := eq_refl.

Example comma_proj_Limit_arrow (L : Limit (comma_proj ◯ K)) :
  (`2 vertex_obj[comma_proj_Limit L])
    = comma_lift_arrow (@limit_cone _ _ _ L) (limit_limitcone L) := eq_refl.

End TwoSided.

(* * ** The arrow 范畴: Mac Lane §V.1 Exercise 3 （已译） *)

Section ArrowLimit.

Context {C : Category}.

Definition arrow_proj_creates_limits {J : Category} (K : J ⟶ @Arrow C) :
  CreatesLimit K comma_proj :=
  comma_proj_CreatesLimit K (Id_PreservesLimitCone (comma_proj2 ◯ K)).

Definition arrow_proj_strictly_creates_limits {J : Category}
  (K : J ⟶ @Arrow C) :
  StrictlyCreatesLimit K comma_proj :=
  comma_proj_StrictlyCreatesLimit K (Id_PreservesLimitCone (comma_proj2 ◯ K)).

Definition arrow_proj_creates_all_limits :
  CreatesAllLimits (@comma_proj C C C Id[C] Id[C]) :=
  fun J K => arrow_proj_creates_limits K.

(* The 推论: arrow 范畴 complete whenever base is, its
 limits computed domains codomains. （已译） *)

Definition Arrow_Complete (HC : @Complete C) : @Complete (@Arrow C) :=
  creates_limits_Complete comma_proj (Product_Complete HC HC)
    arrow_proj_creates_all_limits.

Example Arrow_Complete_dom (HC : @Complete C) {J : Category}
  (K : J ⟶ @Arrow C) :
  fst (`1 vertex_obj[Arrow_Complete HC J K])
    = vertex_obj[HC J (Fst ◯ (comma_proj ◯ K))] := eq_refl.

Example Arrow_Complete_cod (HC : @Complete C) {J : Category}
  (K : J ⟶ @Arrow C) :
  snd (`1 vertex_obj[Arrow_Complete HC J K])
    = vertex_obj[HC J (Snd ◯ (comma_proj ◯ K))] := eq_refl.

End ArrowLimit.
