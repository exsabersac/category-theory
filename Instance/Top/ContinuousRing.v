(* 相关说明。 （已译） *)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Instance.Top.Presheaf.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac RcasesH :=
  unfold Rabs, Rmin, Rmax in *;
  repeat
    match goal with
    | [ |- context[Rcase_abs ?x] ]         => destruct (Rcase_abs x)
    | [ H : context[Rcase_abs ?x] |- _ ]   => destruct (Rcase_abs x)
    | [ |- context[Rle_dec ?x ?y] ]        => destruct (Rle_dec x y)
    | [ H : context[Rle_dec ?x ?y] |- _ ]  => destruct (Rle_dec x y)
    end.
Ltac RlinH := RcasesH; lra.

(*
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.2,
   nLab:      https://ncatlab.org/nlab/show/Top
   Wikipedia: https://en.wikipedia.org/wiki/Ring_(mathematics)

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Balls are open *)

(* 相关说明。 （已译） *)
Lemma ball_around (c d : R) :
  (0 < d)%R → ball_open BS_R (fun r : R => (Rabs (c - r) < d)%R).
Proof.
  intros Hd r Hr.
  exists (d - Rabs (c - r))%R; split.
  - RlinH.
  - intros y Hy; simpl in *.
    RlinH.
Qed.

(* 相关说明。 （已译） *)

Section Pointwise.

Context {X : TopSpace}.

(* Addition, pointwise; continuity by the union-of-intersections
   exhibition (design note 1). *)
Program Definition cr_plus (f g : ContinuousMorphism X R_Top) :
  ContinuousMorphism X R_Top := {|
  continuous_map :=
    {| morphism := fun x => (continuous_map f x + continuous_map g x)%R |}
|}.
Next Obligation.
  intros f g x y Hxy; simpl.
  rewrite (proper_morphism (continuous_map f) x y Hxy).
  rewrite (proper_morphism (continuous_map g) x y Hxy).
  reflexivity.
Qed.
Next Obligation.
  intros f g U HU.
  pose (I := { x : X & U ((continuous_map f x + continuous_map g x)%R) }).
  pose (rad := fun i : I =>
    projT1 (HU ((continuous_map f (projT1 i)
                   + continuous_map g (projT1 i))%R) (projT2 i))).
  apply (open_respects X (fun y =>
    { i : I
    & ((Rabs (continuous_map f (projT1 i) - continuous_map f y)
          < rad i / 2)%R
       ∧ (Rabs (continuous_map g (projT1 i) - continuous_map g y)
            < rad i / 2)%R) })).
  - intro y; split.
    + intros [i [Hf Hg]].
      destruct (HU _ (projT2 i)) as [d [Hd Hball]] eqn:Heq.
      apply Hball; simpl.
      unfold rad in Hf, Hg; rewrite Heq in Hf, Hg; simpl in Hf, Hg.
      RlinH.
    + intro Hy.
      unshelve eexists.
      * exact (y; Hy).
      * simpl; unfold rad; simpl.
        pose proof
          (fst (projT2 (HU ((continuous_map f y + continuous_map g y)%R)
                          Hy))) as Hd.
        assert (Hz : (Rabs (continuous_map f y - continuous_map f y)
                        = 0)%R).
        { replace ((continuous_map f y - continuous_map f y)%R)
            with 0%R by ring.
          exact Rabs_R0. }
        assert (Hz' : (Rabs (continuous_map g y - continuous_map g y)
                         = 0)%R).
        { replace ((continuous_map g y - continuous_map g y)%R)
            with 0%R by ring.
          exact Rabs_R0. }
        split; [ rewrite Hz | rewrite Hz' ];
        exact (Rdiv_lt_0_compat _ _ Hd Rlt_0_2).
  - apply open_union; intro i.
    apply open_inter.
    + apply (continuity f
        (fun v : R =>
           (Rabs (continuous_map f (projT1 i) - v) < rad i / 2)%R)).
      apply ball_around.
      exact (Rdiv_lt_0_compat _ _
               (fst (projT2 (HU ((continuous_map f (projT1 i)
                                    + continuous_map g (projT1 i))%R)
                               (projT2 i)))) Rlt_0_2).
    + apply (continuity g
        (fun v : R =>
           (Rabs (continuous_map g (projT1 i) - v) < rad i / 2)%R)).
      apply ball_around.
      exact (Rdiv_lt_0_compat _ _
               (fst (projT2 (HU ((continuous_map f (projT1 i)
                                    + continuous_map g (projT1 i))%R)
                               (projT2 i)))) Rlt_0_2).
Qed.

(* 相关说明。 （已译） *)
Program Definition cr_mult (f g : ContinuousMorphism X R_Top) :
  ContinuousMorphism X R_Top := {|
  continuous_map :=
    {| morphism := fun x => (continuous_map f x * continuous_map g x)%R |}
|}.
Next Obligation.
  intros f g x y Hxy; simpl.
  rewrite (proper_morphism (continuous_map f) x y Hxy).
  rewrite (proper_morphism (continuous_map g) x y Hxy).
  reflexivity.
Qed.
Next Obligation.
  intros f g U HU.
  pose (I := { x : X & U ((continuous_map f x * continuous_map g x)%R) }).
  pose (M := fun i : I =>
    (Rabs (continuous_map f (projT1 i))
       + Rabs (continuous_map g (projT1 i)) + 1)%R).
  pose (rad := fun i : I =>
    projT1 (HU ((continuous_map f (projT1 i)
                   * continuous_map g (projT1 i))%R) (projT2 i))).
  pose (del := fun i : I => Rmin 1 (rad i / (2 * M i))%R).
  apply (open_respects X (fun y =>
    { i : I
    & ((Rabs (continuous_map f (projT1 i) - continuous_map f y)
          < del i)%R
       ∧ (Rabs (continuous_map g (projT1 i) - continuous_map g y)
            < del i)%R) })).
  - intro y; split.
    + intros [i [Hf Hg]].
      destruct (HU _ (projT2 i)) as [d [Hd Hball]] eqn:Heq.
      apply Hball; simpl.
      unfold del, rad in Hf, Hg; rewrite Heq in Hf, Hg; simpl in Hf, Hg.
      set (fx := (continuous_map f (projT1 i) : R)) in *.
      set (gx := (continuous_map g (projT1 i) : R)) in *.
      set (fy := (continuous_map f y : R)) in *.
      set (gy := (continuous_map g y : R)) in *.
      assert (HM : (0 < Rabs fx + Rabs gx + 1)%R)
        by (pose proof (Rabs_pos fx); pose proof (Rabs_pos gx); lra).
      assert (Hδ1 : (Rabs (fx - fy) < 1)%R)
        by (eapply Rlt_le_trans; [ exact Hf | apply Rmin_l ]).
      assert (Hδd : (Rabs (fx - fy)
                       < d / (2 * (Rabs fx + Rabs gx + 1)))%R)
        by (eapply Rlt_le_trans; [ exact Hf | apply Rmin_r ]).
      assert (Hδd' : (Rabs (gx - gy)
                        < d / (2 * (Rabs fx + Rabs gx + 1)))%R)
        by (eapply Rlt_le_trans; [ exact Hg | apply Rmin_r ]).
      assert (Hfy : (Rabs fy <= Rabs fx + 1)%R).
      { pose proof (Rabs_triang_inv fy fx).
        pose proof (Rabs_minus_sym fx fy).
        lra. }
      assert (Key : (Rabs (fx * gx - fy * gy)
                       <= Rabs fy * Rabs (gx - gy)
                            + Rabs gx * Rabs (fx - fy))%R).
      { replace ((fx * gx - fy * gy)%R)
          with ((fy * (gx - gy) + gx * (fx - fy))%R) by ring.
        pose proof (Rabs_triang (fy * (gx - gy))%R (gx * (fx - fy))%R).
        rewrite Rabs_mult in H.
        rewrite (Rabs_mult gx (fx - fy)%R) in H.
        exact H. }
      simpl.
      assert (Hgxpos := Rabs_pos gx).
      assert (Hfypos := Rabs_pos fy).
      assert (Habs1 := Rabs_pos (gx - gy)%R).
      assert (Habs2 := Rabs_pos (fx - fy)%R).
      clear Heq Hball Hf Hg.
      clearbody fx gx fy gy.
      clear dependent X.
      set (A := (d / (2 * (Rabs fx + Rabs gx + 1)))%R) in *.
      assert (HApos : (0 < A)%R)
        by (apply Rdiv_lt_0_compat; lra).
      assert (Hdiv : ((2 * (Rabs fx + Rabs gx + 1)) * A = d)%R)
        by (unfold A; field; lra).
      clearbody A.
      nra.
    + intro Hy.
      unshelve eexists.
      * exact (y; Hy).
      * simpl; unfold del, rad, M; simpl.
        pose proof
          (fst (projT2 (HU ((continuous_map f y * continuous_map g y)%R)
                          Hy))) as Hd.
        set (d := projT1 (HU ((continuous_map f y
                                 * continuous_map g y)%R) Hy)) in *.
        set (fx := (continuous_map f y : R)) in *.
        set (gx := (continuous_map g y : R)) in *.
        assert (Hz : (Rabs (fx - fx) = 0)%R).
        { replace ((fx - fx)%R) with 0%R by ring.
          exact Rabs_R0. }
        assert (Hz' : (Rabs (gx - gx) = 0)%R).
        { replace ((gx - gx)%R) with 0%R by ring.
          exact Rabs_R0. }
        assert (HM : (0 < Rabs fx + Rabs gx + 1)%R).
        { pose proof (Rabs_pos fx); pose proof (Rabs_pos gx).
          clearbody d fx gx; clear dependent X; lra. }
        assert (Hmin : (0 < Rmin 1 (d / (2 * (Rabs fx + Rabs gx + 1))))%R).
        { apply Rmin_glb_lt; [ exact Rlt_0_1 | ].
          apply Rdiv_lt_0_compat; [ exact Hd | ].
          clearbody d fx gx; clear dependent X; lra. }
        split; [ rewrite Hz | rewrite Hz' ]; exact Hmin.
  - apply open_union; intro i.
    apply open_inter.
    + apply (continuity f
        (fun v : R =>
           (Rabs (continuous_map f (projT1 i) - v) < del i)%R)).
      apply ball_around.
      unfold del, rad, M.
      pose proof
        (fst (projT2 (HU ((continuous_map f (projT1 i)
                             * continuous_map g (projT1 i))%R)
                        (projT2 i)))) as Hd.
      set (fx := (continuous_map f (projT1 i) : R)) in *.
      set (gx := (continuous_map g (projT1 i) : R)) in *.
      set (d := projT1 (HU ((fx * gx)%R) (projT2 i))) in *.
      assert (HM : (0 < Rabs fx + Rabs gx + 1)%R).
      { pose proof (Rabs_pos fx); pose proof (Rabs_pos gx).
        clearbody d fx gx; clear dependent X; lra. }
      apply Rmin_glb_lt; [ exact Rlt_0_1 | ].
      apply Rdiv_lt_0_compat; [ exact Hd | ].
      clearbody d fx gx; clear dependent X; lra.
    + apply (continuity g
        (fun v : R =>
           (Rabs (continuous_map g (projT1 i) - v) < del i)%R)).
      apply ball_around.
      unfold del, rad, M.
      pose proof
        (fst (projT2 (HU ((continuous_map f (projT1 i)
                             * continuous_map g (projT1 i))%R)
                        (projT2 i)))) as Hd.
      set (fx := (continuous_map f (projT1 i) : R)) in *.
      set (gx := (continuous_map g (projT1 i) : R)) in *.
      set (d := projT1 (HU ((fx * gx)%R) (projT2 i))) in *.
      assert (HM : (0 < Rabs fx + Rabs gx + 1)%R).
      { pose proof (Rabs_pos fx); pose proof (Rabs_pos gx).
        clearbody d fx gx; clear dependent X; lra. }
      apply Rmin_glb_lt; [ exact Rlt_0_1 | ].
      apply Rdiv_lt_0_compat; [ exact Hd | ].
      clearbody d fx gx; clear dependent X; lra.
Qed.

(* Negation, pointwise: an isometry, so the same radius works. *)
Program Definition cr_neg (f : ContinuousMorphism X R_Top) :
  ContinuousMorphism X R_Top := {|
  continuous_map :=
    {| morphism := fun x => (- continuous_map f x)%R |}
|}.
Next Obligation.
  intros f x y Hxy; simpl.
  rewrite (proper_morphism (continuous_map f) x y Hxy).
  reflexivity.
Qed.
Next Obligation.
  intros f U HU.
  pose (I := { x : X & U ((- continuous_map f x)%R) }).
  pose (rad := fun i : I =>
    projT1 (HU ((- continuous_map f (projT1 i))%R) (projT2 i))).
  apply (open_respects X (fun y =>
    { i : I
    & (Rabs (continuous_map f (projT1 i) - continuous_map f y)
         < rad i)%R })).
  - intro y; split.
    + intros [i Hf].
      destruct (HU _ (projT2 i)) as [d [Hd Hball]] eqn:Heq.
      apply Hball; simpl.
      unfold rad in Hf; rewrite Heq in Hf; simpl in Hf.
      RlinH.
    + intro Hy.
      unshelve eexists.
      * exact (y; Hy).
      * simpl; unfold rad; simpl.
        pose proof
          (fst (projT2 (HU ((- continuous_map f y)%R) Hy))) as Hd.
        assert (Hz : (Rabs (continuous_map f y - continuous_map f y)
                        = 0)%R).
        { replace ((continuous_map f y - continuous_map f y)%R)
            with 0%R by ring.
          exact Rabs_R0. }
        rewrite Hz; exact Hd.
  - apply open_union; intro i.
    apply (continuity f
      (fun v : R =>
         (Rabs (continuous_map f (projT1 i) - v) < rad i)%R)).
    apply ball_around.
    exact (fst (projT2 (HU ((- continuous_map f (projT1 i))%R)
                          (projT2 i)))).
Qed.

(* 相关说明。 （已译） *)
Program Definition cr_const (c : R) : ContinuousMorphism X R_Top := {|
  continuous_map := {| morphism := fun _ => c |}
|}.
Next Obligation.
  intros c x y Hxy; reflexivity.
Qed.
Next Obligation.
  intros c U HU.
  exact (open_const X (U c)).
Qed.

End Pointwise.

(** ** C(X), as a ring *)

(*
   本节说明 ContinuousRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CRingOb (X : TopSpace) : RingObject := {|
  ring_rig := {|
    rig_setoid := Maps_to_R X;
    rig_zero := cr_const 0%R;
    rig_add := cr_plus;
    rig_one := cr_const 1%R;
    rig_mul := cr_mult;
    rig_prop := @PropEquiv_of_relation _ (is_setoid (Maps_to_R X))
                  (fun f g => forall x : X,
                     @eq R (continuous_map f x) (continuous_map g x))
                  (fun _ _ h => h) (fun _ _ h => h)
  |};
  ring_neg := cr_neg
|}.
Next Obligation.
  intros X f f' Hf g g' Hg x; simpl.
  rewrite (Hf x), (Hg x); reflexivity.
Qed.
Next Obligation.
  intros X f f' Hf g g' Hg x; simpl.
  rewrite (Hf x), (Hg x); reflexivity.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f f' Hf x; simpl.
  rewrite (Hf x); reflexivity.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.

(* * ** Precomposition, 函子 （已译） *)

(* Precomposition along a continuous map is a ring homomorphism: every
   preservation law is pointwise reflexivity, the operations being
   pointwise. *)
Program Definition CRing_precomp {Y X : TopSpace}
  (h : ContinuousMorphism Y X) :
  RigHom (CRingOb X) (CRingOb Y) := {|
  rig_map := {| morphism := fun f => top_compose f h |}
|}.
Next Obligation.
  intros Y X h f f' Hf y; simpl.
  exact (Hf (continuous_map h y)).
Qed.
Next Obligation.
  intros Y X h y; simpl; reflexivity.
Qed.
Next Obligation.
  intros Y X h f g y; simpl; reflexivity.
Qed.
Next Obligation.
  intros Y X h y; simpl; reflexivity.
Qed.
Next Obligation.
  intros Y X h f g y; simpl; reflexivity.
Qed.

(* Mac Lane §II.3 Exercise 5: C, contravariantly, spaces rings.
 The arrow action [contramap] hom 进入 ring 对象 ℝ
 (design note 2). （已译） *)
Program Definition ContinuousRingFunctor : Top^op ⟶ Rng := {|
  fobj := fun X => CRingOb X;
  fmap := fun X Y h => CRing_precomp (unop h)
|}.
Next Obligation.
  intros X Y h h' Hh f y; simpl.
  exact (proper_morphism (continuous_map f) _ _ (Hh y)).
Qed.
Next Obligation.
  intros X f y; simpl; reflexivity.
Qed.
Next Obligation.
  intros X Y Z h h' f y; simpl; reflexivity.
Qed.
