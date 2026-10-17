(*
   本文件为测试：ProbeSolenoid410。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Circle.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Solenoid.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Zp.
Require Import Category.Instance.Top.Solenoid.Presentations.

Generalizable All Variables.

Open Scope category_scope.

(* 相关说明。 （已译） *)

(* The instrument *)
Fail Check p410_absent_name.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p410_circle_points@{o} : top_carrier Circle@{o} = Circle_setoid@{o}
  := eq_refl.

Example p410_wrap_map@{h o | o < h +} (p : positive) :
  continuous_map (wrap@{h o} p) = circ_mul@{o} p := eq_refl.

Example p410_pwrap_map@{o so | o < so +} (p : positive) :
  pmap (pwrap@{o so} p) = circ_mul@{o} p := eq_refl.

Definition p410_wrap_one@{h o | o < h +} :
  wrap@{h o} 1 ≈ @id Top@{h o} Circle@{o} := wrap_one.

(* N1 *)
Fail Example p410_wrap_one_point@{h o | o < h +} (x : CReal) :
  continuous_map (wrap@{h o} 1) x = x := eq_refl.

(* 相关说明。 （已译） *)
Definition p410_circ_prop@{o} : PropEquiv@{o o} (is_setoid Circle_setoid@{o})
  := circ_PropEquiv.

Definition p410_circle_two@{o} :
  @equiv _ Circle_setoid@{o} (inject_Q (1 # 2)) (inject_Q 0) → False :=
  circle_half_not_zero.

Definition p410_circle_lift@{h o hs | o < h, h < hs +} :
  @Isomorphism Sets@{h hs} (Setoid_Lift@{o h} Circle_setoid@{o})
    Circle_setoid@{h} := circle_lift_iso.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p410_init_family_up@{o o1 | o < o1 +} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o1} :=
  ∀ T : (S → Type@{o}) → Type@{o},
    (∀ n (U : X n → Type@{o}), IsOpen (X n) U → T (fun s => U (t n s))) →
    T V.

Definition p410_init_union_up@{o o1 | o < o1 +} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o1} :=
  ∀ s, V s → { n : nat & { U : X n → Type@{o} &
     (IsOpen (X n) U * U (t n s) * ∀ s', U (t n s') → V s')%type } }.

(* N2 *)
Fail Definition p410_init_family@{o} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o} :=
  ∀ T : (S → Type@{o}) → Type@{o},
    (∀ n (U : X n → Type@{o}), IsOpen (X n) U → T (fun s => U (t n s))) →
    T V.

(* N3 *)
Fail Definition p410_init_union@{o} (S : SetoidObject@{o o})
  (X : nat → TopSpace@{o}) (t : ∀ n, SetoidMorphism@{o o o} S (X n))
  (V : S → Type@{o}) : Type@{o} :=
  ∀ s, V s → { n : nat & { U : X n → Type@{o} &
     (IsOpen (X n) U * U (t n s) * ∀ s', U (t n s') → V s')%type } }.

(* CONTROL: solenoid's own topology sits at points' universe, and
 it limit [Top], characterised 普遍性质. （已译） *)
Definition p410_solenoid_space@{s o so | o < so +} (p : positive) :
  TopSpace@{o} := Solenoid@{s o so} p.

Definition p410_limit@{s o so h r | o < so, o < h +} (p : positive) :
  Limit@{r s h h} (CircleTower@{s h o} p) := solenoid_limit@{s o so h r} p.

Definition p410_universal@{s o so h + | o < so, o < h +} (p : positive)
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} Z (SolPoints@{s o so} p)) :
  Continuous@{h o} Z (Solenoid@{s o so} p) g ↔
  (∀ j, Continuous@{h o} Z Circle@{o}
          (setoid_morphism_compose (sol_pr p j) g)) :=
  solenoid_universal p Z g.

Definition p410_forget@{s o so h hs + | o < so, o < h, h < hs +}
  (p : positive) :
  IsLimitCone (FCone Top_Forget@{o h hs} (sol_cone@{s o so h} p)) :=
  solenoid_forget_preserves p.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p410_points@{s o so h + | o < so, o < h +} (p : positive) :
  top_carrier (vertex_obj[@limit_cone _ _ _ (solenoid_limit@{s o so h _} p)])
  = inverse_limit (UCircleTower@{s o so} p) := eq_refl.

Example p410_legs@{s o so h + | o < so, o < h +} (p : positive) (n : nat) :
  continuous_map
    (cone_leg (@limit_cone _ _ _ (solenoid_limit@{s o so h _} p)) n)
  = tower_proj (UCircleTower@{s o so} p) n := eq_refl.

Example p410_compat@{s o so + | o < so +} (p : positive)
  (x : Sets_iprod_obj (fun n : nat => fobj[UCircleTower@{s o so} p] n)) :
  tower_compat (UCircleTower@{s o so} p) x
  = (∀ n : nat, circ_eq (CReal_mult (posR p) (x (S n))) (x n)) := eq_refl.

Example p410_ppoints@{s o so + | o < so +} (p : positive) :
  pt_carrier (PSolenoid@{s o so _} p)
  = inverse_limit (PForget@{o so} ◯ PCircleTower@{s o so} p) := eq_refl.

Example p410_carriers@{s o so + | o < so +} (p : positive) :
  carrier (SolPoints@{s o so} p)
  = carrier (pt_carrier (PSolenoid@{s o so _} p)) := eq_refl.

(*
   本节说明 ProbeSolenoid410 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition p410_tower_obj (F : Omega^op ⟶ Sets) : obj[Sets] := {|
  carrier   := { x : Sets_iprod_obj (fun n : nat => F n) & tower_compat F x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p n; reflexivity.
  - intros p q Hpq n; symmetry; exact (Hpq n).
  - intros p q r Hpq Hqr n; transitivity (`1 q n);
    [exact (Hpq n)|exact (Hqr n)].
Defined.

Example p410_flip_ptop (p : positive) :
  p410_tower_obj (UCircleTower p) = p410_tower_obj (PForget ◯ PCircleTower p)
  := eq_refl.

Example p410_flip_group (p : positive) :
  p410_tower_obj (UCircleTower p)
  = p410_tower_obj (Ab_Forget ◯ GroupTower p) := eq_refl.

(* N4 *)
Fail Example p410_points_ptop (p : positive) :
  inverse_limit (UCircleTower p) = inverse_limit (PForget ◯ PCircleTower p)
  := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p410_endo_step {C : Category} (X : obj[C]) (w : X ~{C}~> X)
  (n : nat) : fmap[EndoTower X w] (omega_step n) = id ∘ w := eq_refl.

Definition p410_endo_step_equiv {C : Category} (X : obj[C])
  (w : X ~{C}~> X) (n : nat) : fmap[EndoTower X w] (omega_step n) ≈ w :=
  endo_step_equiv X w n.

(* N5 *)
Fail Example p410_endo_step_w {C : Category} (X : obj[C])
  (w : X ~{C}~> X) (n : nat) : fmap[EndoTower X w] (omega_step n) = w
  := eq_refl.

(* CONTROL: Mac Lane's tower read back through [tower_step] with an
   extensible universe list. *)
Example p410_tower_step@{s h o + | o < h +} (p : positive) (n : nat) :
  fmap[CircleTower@{s h o} p] (tower_step n) = id ∘ wrap p := eq_refl.

(* N6 *)
Fail Example p410_tower_step_closed@{s h o | o < h} (p : positive)
  (n : nat) : fmap[CircleTower@{s h o} p] (tower_step n) = id ∘ wrap p
  := eq_refl.

(* 相关说明。 （已译） *)

(* CONTROL: two points every p, read back through [Defined]
 witness; leg at stage 0 not injective 1 < p; solenoid at
 p = 1 isomorphic circle both 范畴. （已译） *)
Definition p410_two_points@{s o so | o < so +} (p : positive) :
  @equiv _ (SolPoints@{s o so} p) (zero_string@{s o so} p)
    (half_string@{s o so} p) → False := solenoid_two_points p.

Example p410_two_points_first@{s o so + | o < so +} (p : positive) :
  projT1 (PTop_solenoid_two_points p) = zero_string@{s o so} p
  := eq_refl.

Definition p410_mu0@{s o so | o < so +} (p : positive) (Hp : (1 < p)%positive) :
  (sol_pr@{s o so} p 0 (unit_string p) ≈ sol_pr p 0 (zero_string p)) *
  (@equiv _ (SolPoints@{s o so} p) (unit_string p) (zero_string p) → False) :=
  (unit_string_over_zero p, unit_string_not_zero p Hp).

Definition p410_one_iso@{s o so h | o < so, o < h +} :
  @Isomorphism Top@{h o} (Solenoid@{s o so} 1) Circle@{o} := solenoid_one_iso.

Definition p410_pone_iso@{s o so r | o < so +} :
  @Isomorphism PTopCat@{o so} (PSolenoid@{s o so r} 1) PCircle@{o} :=
  PTop_solenoid_one_iso.

(* 相关说明。 （已译） *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p410_towers_agree@{s u o so +} (p : positive) :
  PForget@{o so} ◯ PCircleTower@{s o so} p
    ≈ Ab_Forget@{u so o} ◯ GroupTower@{s u o} p := towers_agree p.

Example p410_group_points@{s u o so r | o < u, o < so +} (p : positive) :
  Ab_Forget@{u so o} (GSolenoid@{s u o so r} p)
  = inverse_limit (Ab_Forget@{u so o} ◯ GroupTower@{s u o} p) := eq_refl.

Definition p410_points_iso@{s u o so r | o < u, o < so +} (p : positive) :
  SolPoints@{s o so} p
    ≅[Sets@{o so}] Ab_Forget@{u so o} (GSolenoid@{s u o so r} p) :=
  solenoid_points_iso p.

(* N7 *)
Fail Example p410_points_group@{s u o so r | o < u, o < so +}
  (p : positive) :
  SolPoints@{s o so} p = Ab_Forget@{u so o} (GSolenoid@{s u o so r} p)
  := eq_refl.

(* 相关说明。 （已译） *)
Example p410_fibre_carrier@{s u o so r | o < u, o < so +} (p : positive) :
  carrier (cmon_setoid (SolFibre@{s u o so r} p))
  = { x : SolPoints@{s o so} p &
      circ_eq@{o} (sol_pr@{s o so} p 0 x) (inject_Q 0) } := eq_refl.

Definition p410_Zp_iso@{s u o so r | o < u, o < so +} (p : positive)
  (Hp : (1 < p)%positive) :
  @Isomorphism Ab@{u o} (ZpAb@{s o so} p) (SolFibre@{s u o so r} p) :=
  Zp_fibre_iso p Hp.

Example p410_zp_one@{s u o so r | o < u, o < so +} (p : positive)
  (Hp : (1 < p)%positive) :
  `1 (projT1 (cmon_map (zp_to_fibre@{s u o so r} p Hp)
                (rig_one (Zp@{o o o o so s so o so} ZComm@{o o o} (Zpos p)))))
  = `1 (unit_string@{s o so} p) := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p410_pcover@{o so | o < so +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  @Isomorphism PTopCat@{o so} (SheetSpace@{o} p y k) (ArcSpace@{o} y) :=
  pwrap_sheet_iso p y k Hk.

Example p410_pcover_to@{o so | o < so +} (p : positive) (y : CReal)
  (k : Z) (Hk : (0 <= k < Zpos p)%Z) (b : SheetSpace@{o} p y k) :
  proj1_sig (pmap (to (pwrap_sheet_iso@{o so} p y k Hk)) b)
  = circ_mul@{o} p (proj1_sig b) := eq_refl.

(*
   本节说明 ProbeSolenoid410 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p410_tarc_space@{o} (y : CReal) : TopSpace@{o} := TArc@{o} y.

Definition p410_csub_universal@{h o | o < h +}
  (P : Circle_setoid@{o} → Type@{o}) (Z : TopSpace@{o})
  (g : SetoidMorphism@{o o o} Z (csub_setoid@{o} P)) :
  Continuous@{h o} Z (CSub@{o} P) g ↔
  Continuous@{h o} Z Circle@{o} (setoid_morphism_compose (csub_incl_map P) g)
  := csub_universal P Z g.

Example p410_arc_squash@{o} (y x : CReal) :
  in_arc@{o} y x = inhabited (cint@{o} y (1 # 4) x) := eq_refl.

Definition p410_cover@{h o | o < h +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) :
  @Isomorphism Top@{h o} (TSheet@{o} p y k) (TArc@{o} y) :=
  wrap_sheet_iso p y k Hk.

Example p410_cover_to@{h o | o < h +} (p : positive) (y : CReal) (k : Z)
  (Hk : (0 <= k < Zpos p)%Z) (b : TSheet@{o} p y k) :
  projT1 (continuous_map (to (wrap_sheet_iso@{h o} p y k Hk)) b)
  = circ_mul@{o} p (projT1 b) := eq_refl.

Definition p410_evenly@{o} (p : positive) (y : CReal) :
  (IsOpen Circle@{o} (tarc@{o} y) * tarc@{o} y y *
   (∀ k, IsOpen Circle@{o} (tsheet@{o} p y k)) *
   (∀ k k' (z : Circle_setoid@{o}),
      tsheet@{o} p y k z → tsheet@{o} p y k' z → k = k') *
   (∀ z : Circle_setoid@{o}, tarc@{o} y (CReal_mult (posR p) z)
      ↔ { k : Z & ((0 <= k < Zpos p)%Z * tsheet@{o} p y k z)%type }))%type
  := wrap_evenly_covered p y.

(* 相关说明。 （已译） *)
Definition p410_tsub_arc_whole@{o o1 | o < o1 +} (y : CReal) :
  tsub_open@{o o1} Circle@{o} (csub_setoid@{o} (tarc@{o} y))
    (csub_incl_map@{o} (tarc@{o} y)) (fun _ => poly_unit@{o}) :=
  tsub_open_whole Circle (csub_setoid (tarc y)) (csub_incl_map (tarc y)).

(* N8 *)
Fail Definition p410_tsub_arc@{o o1 | o < o1 +} (y : CReal) :
  TopSpace@{o} := {|
  top_carrier   := csub_setoid@{o} (tarc@{o} y);
  IsOpen        := tsub_open@{o o1} Circle@{o} (csub_setoid@{o} (tarc@{o} y))
                     (csub_incl_map@{o} (tarc@{o} y));
  open_respects := tsub_open_respects Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_proper   := tsub_open_proper Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_union    := tsub_open_union Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_whole    := tsub_open_whole Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y));
  open_inter    := tsub_open_inter Circle (csub_setoid (tarc y))
                     (csub_incl_map (tarc y))
|}.

(* 相关说明。 （已译） *)

Print Assumptions solenoid_limit.
Print Assumptions CircleGroup.
Print Assumptions Zp_fibre_iso.
Print Assumptions wrap_sheet_iso.
Print Assumptions pwrap_sheet_iso.

(* 相关说明。 （已译） *)

(* Instance/Top/Circle.v: 94 names. *)
Check cball.
Check cball_mono.
Check cball_mul.
Check cball_of_eq.
Check cball_of_rball.
Check cball_open.
Check cball_triang.
Check cint.
Check cint_balls.
Check cint_centre.
Check cint_open.
Check cint_sub.
Check circ_eq.
Check circ_eq_of_creal.
Check circ_eq_of_peq.
Check circ_eq_refl.
Check circ_eq_sym.
Check circ_eq_trans.
Check circ_eq_translate.
Check circ_eq_witness_unique.
Check circ_mul.
Check circ_peq.
Check circ_peq_of_eq.
Check circ_PropEquiv.
Check circ_q.
Check circ_setoid.
Check Circle.
Check Circle.circ_mul_obligation_1.
Check Circle.circ_q_obligation_1.
Check Circle.circ_setoid_obligation_1.
Check Circle.circle_lift_iso_obligation_1.
Check Circle.circle_lift_iso_obligation_2.
Check Circle.circle_lift_iso_obligation_3.
Check Circle.circle_lift_iso_obligation_4.
Check Circle.creal_setoid_obligation_1.
Check Circle.line_mul_obligation_1.
Check circle_half_not_zero.
Check circle_lift_iso.
Check circle_open_balls.
Check Circle_points.
Check Circle_setoid.
Check creal_inject_Q_injective.
Check creal_inject_Z_injective.
Check creal_inject_Z_mult.
Check creal_minus_self.
Check creal_setoid.
Check cround.
Check cround_ball.
Check cround_between.
Check cround_spec.
Check inject_Q_minus.
Check inject_Q_minus_int.
Check inject_Q_minus_int_inv.
Check inject_Q_pos_le.
Check line_mul.
Check line_mul_cont.
Check pcball_open.
Check PCircle.
Check pcircle_open_balls.
Check PCircle_points.
Check pline_mul_cont.
Check posR.
Check posR_nonneg.
Check PRLine.
Check prline_mul.
Check propen.
Check propen_inter.
Check propen_proper.
Check propen_respects.
Check propen_union.
Check propen_whole.
Check pwrap.
Check pwrap_map.
Check pwrap_one.
Check q_half_half.
Check q_half_pos.
Check q_scale_pos.
Check rball.
Check rball_center.
Check rball_mono.
Check rball_mul.
Check rball_of_cball.
Check RLine.
Check rline_mul.
Check RLine_setoid.
Check ropen.
Check ropen_inter.
Check ropen_proper.
Check ropen_respects.
Check ropen_union.
Check ropen_whole.
Check wrap.
Check wrap_map.
Check wrap_one.

(* Instance/Top/Solenoid.v: 78 names. *)
Check CircleTower.
Check CircleTower_step.
Check const_string_cont.
Check const_string_map.
Check endo_hom.
Check endo_hom_comp.
Check endo_hom_fmap.
Check endo_hom_id.
Check endo_hom_respects.
Check endo_hom_trans.
Check endo_step.
Check endo_step_equiv.
Check EndoTower.
Check EndoTower_map.
Check half_string.
Check half_string_coord.
Check one_compat.
Check open_bounded_inter.
Check PCircleTower.
Check PCircleTower_points.
Check PCircleTower_step.
Check pconst_string_cont.
Check pconst_string_map.
Check posR_scale.
Check ppow.
Check psol_leg.
Check PSolenoid.
Check PTop_solenoid_coarsest.
Check PTop_solenoid_forget_preserves.
Check PTop_solenoid_leg_map.
Check PTop_solenoid_limit.
Check PTop_solenoid_one_iso.
Check PTop_solenoid_open_forced.
Check PTop_solenoid_points.
Check PTop_solenoid_two_points.
Check PTop_solenoid_universal.
Check scaled_compat.
Check sol_acone.
Check sol_compat.
Check sol_cone.
Check sol_forget_med.
Check sol_leg.
Check sol_leg_cont.
Check sol_lift_cont.
Check sol_med.
Check sol_med_map.
Check sol_pr.
Check sol_tower_compat.
Check Solenoid.
Check Solenoid.const_string_map_obligation_1.
Check Solenoid.pconst_string_map_obligation_1.
Check Solenoid.sol_forget_med_obligation_1.
Check Solenoid.sol_med_map_obligation_1.
Check Solenoid.solenoid_limit_obligation_1.
Check Solenoid.solenoid_limit_obligation_2.
Check solenoid_coarsest.
Check solenoid_forget_preserves.
Check solenoid_leg_map.
Check solenoid_limit.
Check solenoid_one_iso.
Check solenoid_points.
Check solenoid_points_agree.
Check solenoid_two_points.
Check solenoid_universal.
Check SolPoints.
Check sopen.
Check sopen_inter.
Check sopen_proper.
Check sopen_respects.
Check sopen_union.
Check sopen_whole.
Check string_one_const.
Check UCircleTower.
Check unit_string.
Check unit_string_not_zero.
Check unit_string_over_zero.
Check zero_compat.
Check zero_string.

(* Instance/Top/Solenoid/Presentations.v: 164 names. *)
Check arc_shift.
Check ArcSpace.
Check circ_mul_sheet_lift.
Check circ_pow.
Check circ_pow_map.
Check CircleGroup.
Check CircleTower_points.
Check creal_fibre_add.
Check creal_recover.
Check creal_scale_back.
Check CSub.
Check csub_coarsest.
Check csub_incl.
Check csub_incl_cont.
Check csub_incl_map.
Check csub_lift_cont.
Check csub_open.
Check csub_open_inter.
Check csub_open_proper.
Check csub_open_respects.
Check csub_open_union.
Check csub_open_whole.
Check csub_setoid.
Check csub_universal.
Check dpow_ppow.
Check fibre_coord.
Check fibre_coord_spec.
Check fibre_exhaust.
Check fibre_int.
Check fibre_int_spec.
Check fibre_int_step.
Check fibre_pt.
Check fibre_pt_distinct.
Check fibre_pt_over.
Check fibre_real_base.
Check fibre_real_diff.
Check fibre_real_step.
Check fibre_real_sum.
Check fibre_real_zero.
Check fibre_to_zp.
Check fibre_to_zp_map.
Check fibre_to_zp_pt.
Check group_solenoid_points.
Check group_step_fn.
Check GroupSolenoid.
Check GroupTower.
Check GroupTower_points.
Check GroupTower_step.
Check gsol_leg.
Check gsol_leg_map.
Check gsol_neg_coord.
Check gsol_plus_coord.
Check gsol_zero_coord.
Check GSolenoid.
Check in_arc.
Check in_arc_centre.
Check in_arc_open.
Check in_arc_shift.
Check in_arc_squash.
Check in_sheet.
Check in_sheet_disjoint.
Check in_sheet_open.
Check in_sheet_preimage.
Check int_near_zero.
Check inv_p_mul.
Check inv_p_unit.
Check mul_ball.
Check p_sheet_lift.
Check Presentations.circ_pow_obligation_1.
Check Presentations.circ_pow_obligation_2.
Check Presentations.CircleGroup_obligation_1.
Check Presentations.CircleGroup_obligation_2.
Check Presentations.CircleGroup_obligation_3.
Check Presentations.CircleGroup_obligation_4.
Check Presentations.CircleGroup_obligation_5.
Check Presentations.CircleGroup_obligation_6.
Check Presentations.csub_incl_map_obligation_1.
Check Presentations.csub_setoid_obligation_1.
Check Presentations.fibre_to_zp_map_obligation_1.
Check Presentations.fibre_to_zp_obligation_1.
Check Presentations.fibre_to_zp_obligation_2.
Check Presentations.pwrap_sheet_iso_obligation_1.
Check Presentations.pwrap_sheet_iso_obligation_2.
Check Presentations.pwrap_sheet_map_obligation_1.
Check Presentations.sheet_lift_map_obligation_1.
Check Presentations.solenoid_points_iso_obligation_1.
Check Presentations.solenoid_points_iso_obligation_2.
Check Presentations.solenoid_points_iso_obligation_3.
Check Presentations.solenoid_points_iso_obligation_4.
Check Presentations.tsheet_lift_map_obligation_1.
Check Presentations.wrap_sheet_iso_obligation_1.
Check Presentations.wrap_sheet_iso_obligation_2.
Check Presentations.wrap_sheet_map_obligation_1.
Check Presentations.Zp_fibre_iso_obligation_1.
Check Presentations.Zp_fibre_iso_obligation_2.
Check Presentations.zp_to_fibre_map_obligation_1.
Check Presentations.zp_to_fibre_obligation_1.
Check Presentations.zp_to_fibre_obligation_2.
Check pspace_step_fn.
Check pwrap_evenly_covered.
Check pwrap_sheet.
Check pwrap_sheet_cont.
Check pwrap_sheet_iso.
Check pwrap_sheet_iso_to.
Check pwrap_sheet_map.
Check q_fibre_add.
Check q_fibre_base.
Check q_fibre_diff.
Check q_fibre_split.
Check q_fibre_step.
Check q_fibre_unit.
Check q_fibre_zero.
Check q_p_pos.
Check q_quarter_half.
Check q_scale_le.
Check qmin_pos.
Check sheet_index.
Check sheet_lift.
Check sheet_lift_cont.
Check sheet_lift_in.
Check sheet_lift_lip.
Check sheet_lift_map.
Check sheet_lift_mor.
Check sheet_lift_respects.
Check sheet_lift_wrap.
Check SheetSpace.
Check sol_fibre_carrier.
Check solenoid_carriers_agree.
Check solenoid_equiv_agree.
Check solenoid_points_iso.
Check SolFibre.
Check space_step_fn.
Check tarc.
Check TArc.
Check tarc_centre.
Check tarc_open.
Check towers_agree.
Check tsheet.
Check TSheet.
Check tsheet_disjoint.
Check tsheet_lift_cont.
Check tsheet_lift_in.
Check tsheet_lift_map.
Check tsheet_lift_mor.
Check tsheet_open.
Check tsheet_preimage.
Check wrap_evenly_covered.
Check wrap_sheet.
Check wrap_sheet_cont.
Check wrap_sheet_iso.
Check wrap_sheet_iso_to.
Check wrap_sheet_map.
Check zp_coord.
Check zp_coord_base.
Check zp_coord_compat.
Check zp_coord_respects.
Check Zp_fibre_iso.
Check zp_one_to_unit_string.
Check zp_string.
Check zp_to_fibre.
Check zp_to_fibre_coord.
Check zp_to_fibre_map.
Check ZpAb.
Check zres_of_eq.
