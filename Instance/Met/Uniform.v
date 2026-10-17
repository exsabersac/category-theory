Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.
Require Import Category.Instance.Met.Completion.

Generalizable All Variables.

Open Scope R_scope.

(** * Metric spaces with uniformly continuous maps; Mac Lane §IV.3 *)

(*
 nLab:  https://ncatlab.org/nlab/show/complete+metric+space
 nLab:  https://ncatlab.org/nlab/show/uniformly+continuous+map
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book:  Mac Lane, same, §IV.3, printed p. 91 (PDF p. 100) — the
 Book:  Bishop, "Foundations of Constructive Analysis", McGraw-Hill

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Uniformly continuous maps *)

Definition UCont@{o +} (X Y : MetricSpace@{o})
  (f : SetoidMorphism (met_carrier X) (met_carrier Y)) : Type@{o} :=
  ∀ eps : R, 0 < eps →
    ∃ delta : R, (0 < delta ∧
      ∀ x y : X, dist x y < delta → dist (f x) (f y) < eps).

Record UMap@{o +} (X Y : MetricSpace@{o}) : Type@{o} := {
  umap :> SetoidMorphism (met_carrier X) (met_carrier Y);
  umap_uc : UCont X Y umap
}.

Arguments umap {X Y} _.
Arguments umap_uc {X Y} _ _ _.

Definition UMap_equiv@{o +} {X Y : MetricSpace@{o}} : crelation (UMap X Y) :=
  fun f g => ∀ x : X, umap f x ≈ umap g x.

Arguments UMap_equiv {X Y} _ _ /.

#[export]
Program Instance UMap_Setoid@{o +} {X Y : MetricSpace@{o}} :
  Setoid (UMap X Y) := {| equiv := UMap_equiv |}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (umap g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

(** ** The category MetU *)

Definition umet_id@{o +} {X : MetricSpace@{o}} : UMap X X.
Proof.
  refine {| umap := setoid_morphism_id |}.
  intros eps Heps; exists eps; split; [ exact Heps |].
  intros x y H; exact H.
Defined.

Definition umet_compose@{o +} {X Y Z : MetricSpace@{o}}
  (g : UMap Y Z) (f : UMap X Y) : UMap X Z.
Proof.
  refine {| umap := setoid_morphism_compose g f |}.
  intros eps Heps.
  destruct (umap_uc g eps Heps) as [dg [Hdg Hg]].
  destruct (umap_uc f dg Hdg) as [df [Hdf Hf]].
  exists df; split; [ exact Hdf |].
  intros x y Hxy; simpl.
  apply Hg, Hf, Hxy.
Defined.

Lemma umet_compose_respects@{o +} {X Y Z : MetricSpace@{o}} :
  Proper (equiv ==> equiv ==> equiv) (@umet_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (umap f1 x)).
  apply proper_morphism, Hf.
Qed.

Program Definition MetU@{u o | o < u +} : Category@{u o o} := {|
  obj     := MetricSpace@{o};
  hom     := UMap;
  homset  := @UMap_Setoid;
  id      := @umet_id;
  compose := @umet_compose;

  compose_respects := @umet_compose_respects
|}.

(** ** The complete spaces, a full subcategory *)

Definition CompleteSpacesU@{u o +} : Subcategory MetU@{u o} :=
  @Build_Subcategory MetU
    (fun X => MComplete X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CMetU@{u o +} : Category := Sub MetU@{u o} CompleteSpacesU.

Definition CMetU_Incl@{u o +} : Sub MetU@{u o} CompleteSpacesU ⟶ MetU@{u o} :=
  Incl MetU CompleteSpacesU.

Definition CMetU_Full@{u o +} :
  Construction.Subcategory.Full MetU@{u o} CompleteSpacesU :=
  fun _ _ _ _ _ => I.

(** ** Isometries are uniformly continuous: the comparison Met ⟶ MetU *)

Definition iso_umap@{o +} {X Y : MetricSpace@{o}} (f : Isometry X Y) :
  UMap X Y.
Proof.
  refine {| umap := isometry_map f |}.
  intros eps Heps; exists eps; split; [ exact Heps |].
  intros x y H; rewrite (isometry_dist f x y); exact H.
Defined.

Program Definition Met_to_MetU@{u o | o < u +} : Met@{u o} ⟶ MetU@{u o} := {|
  fobj := fun X => X;
  fmap := fun X Y f => iso_umap f
|}.

Example Met_to_MetU_obj@{u o | o < u +} (X : Met@{u o}) :
  fobj[Met_to_MetU@{u o}] X = X := eq_refl.

Lemma Met_to_MetU_Faithful@{u o | o < u +} : Faithful Met_to_MetU@{u o}.
Proof. constructor; intros X Y f g H x; exact (H x). Qed.

(* A constant map is uniformly continuous. *)
Definition const_umap@{o +} (X Y : MetricSpace@{o}) (b : Y) : UMap X Y.
Proof.
  unshelve refine {| umap := {| morphism := fun _ => b |} |}.
  - repeat intro; reflexivity.
  - intros eps Heps; exists 1; split; [ lra |].
    intros; simpl; rewrite dist_refl; exact Heps.
Defined.

Theorem Met_to_MetU_not_Full@{u | Set < u +} :
  Functor.Full Met_to_MetU@{u Set} → False.
Proof.
  intros HF.
  pose (c := const_umap Harmonic Harmonic 0%nat).
  pose (f := @prefmap _ _ _ HF Harmonic Harmonic c).
  pose proof (@fmap_sur _ _ _ HF Harmonic Harmonic c) as Hf.
  assert (H01 : isometry_map f 0%nat ≈ isometry_map f 1%nat).
  { transitivity (umap c 0%nat).
    - exact (Hf 0%nat).
    - symmetry; exact (Hf 1%nat). }
  pose proof (isometry_injective f 0%nat 1%nat H01) as H.
  discriminate H.
Qed.

(** ** Uniformly continuous maps preserve limits *)

Lemma umap_MConverges@{o +} {X Y : MetricSpace@{o}} (f : UMap X Y)
  (u : nat → X) (l : X) :
  MConverges X u l → MConverges Y (fun n => umap f (u n)) (umap f l).
Proof.
  intros Hl eps Heps.
  destruct (umap_uc f eps Heps) as [d [Hd Hf]].
  destruct (Hl d Hd) as [N HN].
  exists N; intros n Hn.
  apply Hf, HN, Hn.
Defined.

(* A non-negative real below every positive real is zero. *)
Lemma ureal_below_all_zero@{+} (r : R) :
  0 <= r → (∀ eps, 0 < eps → r < eps) → r = 0.
Proof.
  intros H0 H.
  destruct (Rle_lt_or_eq_dec 0 r H0) as [Hlt | Heq]; [| now symmetry].
  specialize (H r Hlt); lra.
Qed.

(** ** The extension of a uniformly continuous map to the completion *)

Section Extend.

Local Set Default Proof Using "All".

Universe o.

Context (X Y : MetricSpace@{o}).
Context (cY : MComplete Y).
Context (f : UMap X Y).

Definition uext_seq (x : Completion X) : nat → Y :=
  fun n => umap f (cs_seq X x n).

(* Uniform continuity alone carries a Cauchy sequence to a Cauchy
   sequence: the section's completeness hypothesis is not used, and the
   explicit [Proof using] keeps it out of the lemma's type. *)
Definition uext_MCauchy (x : Completion X) : MCauchy Y (uext_seq x).
Proof using X Y f.
  intros eps Heps.
  destruct (umap_uc f eps Heps) as [d [Hd Hf]].
  destruct (cs_cauchy X x d Hd) as [N HN].
  exists N; intros m n Hm Hn.
  apply Hf, HN; assumption.
Defined.

Definition uext_val (x : Completion X) : Y := `1 (cY _ (uext_MCauchy x)).

Definition uext_spec (x : Completion X) :
  MConverges Y (uext_seq x) (uext_val x) := `2 (cY _ (uext_MCauchy x)).

Lemma uext_close (x y : Completion X) (eps : R) (Heps : 0 < eps) (d : R)
  (Hf : ∀ a b : X, dist a b < d → dist (umap f a) (umap f b) < eps / 2)
  (N : nat)
  (HN : ∀ n, (N <= n)%nat → dist (cs_seq X x n) (cs_seq X y n) < d) :
  dist (uext_val x) (uext_val y) < eps.
Proof.
  destruct (uext_spec x (eps / 8) ltac:(lra)) as [N1 H1].
  destruct (uext_spec y (eps / 8) ltac:(lra)) as [N2 H2].
  pose (n := Nat.max N (Nat.max N1 N2)).
  assert (N <= n)%nat as HnN by apply Nat.le_max_l.
  assert (N1 <= n)%nat as Hn1
    by (transitivity (Nat.max N1 N2);
        [ apply Nat.le_max_l | apply Nat.le_max_r ]).
  assert (N2 <= n)%nat as Hn2
    by (transitivity (Nat.max N1 N2);
        [ apply Nat.le_max_r | apply Nat.le_max_r ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  pose proof (Hf _ _ (HN n HnN)) as Hmid.
  pose proof (dist_triangle (uext_val x) (uext_seq x n) (uext_val y)) as T1.
  pose proof (dist_triangle (uext_seq x n) (uext_seq y n) (uext_val y)) as T2.
  rewrite (dist_sym (uext_val x) (uext_seq x n)) in T1.
  unfold uext_seq in *.
  lra.
Qed.

Lemma uext_proper (x y : Completion X) : x ≈ y → uext_val x ≈ uext_val y.
Proof.
  intro Hxy.
  apply dist_separates, ureal_below_all_zero; [ apply dist_nonneg |].
  intros eps Heps.
  destruct (umap_uc f (eps / 2) ltac:(lra)) as [d [Hd Hf]].
  destruct (Hxy d Hd) as [N HN].
  apply (uext_close x y eps Heps d Hf N).
  intros n Hn; specialize (HN n Hn).
  unfold R_dist, cdist_seq in HN.
  rewrite Rminus_0_r in HN.
  eapply Rle_lt_trans; [ apply Rle_abs | exact HN ].
Qed.

Definition uext_morphism :
  SetoidMorphism (met_carrier (Completion X)) (met_carrier Y).
Proof.
  unshelve refine {| morphism := uext_val |}.
  intros x y Hxy; exact (uext_proper x y Hxy).
Defined.

Definition uext_uc : UCont (Completion X) Y uext_morphism.
Proof.
  intros eps Heps.
  destruct (umap_uc f (eps / 2) ltac:(lra)) as [d [Hd Hf]].
  exists d; split; [ exact Hd |].
  intros x y Hxy; simpl.
  change (cdist X x y < d) in Hxy.
  destruct (cdist_spec X x y (d - cdist X x y) ltac:(lra)) as [N HN].
  apply (uext_close x y eps Heps d Hf N).
  intros n Hn; specialize (HN n Hn).
  unfold R_dist in HN.
  destruct (Rabs_def2 _ _ HN) as [Hhi _].
  unfold cdist_seq in Hhi.
  lra.
Defined.

Definition uext : UMap (Completion X) Y := {|
  umap := uext_morphism; umap_uc := uext_uc |}.

Lemma uext_eta (a : X) : umap uext (eta_seq X a) ≈ umap f a.
Proof.
  apply (MConverges_unique (uext_seq (eta_seq X a))).
  - exact (uext_spec (eta_seq X a)).
  - intros eps Heps.
    exists 0%nat; intros n _.
    unfold uext_seq; simpl.
    rewrite dist_refl; exact Heps.
Qed.

Lemma uext_unique (g : UMap (Completion X) Y) :
  (∀ a : X, umap g (eta_seq X a) ≈ umap f a) →
  ∀ x : Completion X, umap g x ≈ umap uext x.
Proof.
  intros Hg x.
  apply (MConverges_unique (uext_seq x)).
  - apply (MConverges_respects_seq
             (fun n => umap g (eta_seq X (cs_seq X x n))) (uext_seq x)).
    + intro n; exact (Hg (cs_seq X x n)).
    + exact (umap_MConverges g _ x (eta_dense X x)).
  - exact (uext_spec x).
Qed.

End Extend.

(** ** The completion as a universal arrow in MetU *)

Definition CompletionU@{u o +} (X : MetricSpace@{o}) :
  Sub MetU@{u o} CompleteSpacesU :=
  (Completion X; Completion_MComplete X).

Definition etaU@{o +} (X : MetricSpace@{o}) : UMap X (Completion X) :=
  iso_umap (eta X).

Definition CompletionU_UniversalArrow@{u o +} (X : MetU@{u o}) :
  UniversalArrow X (Incl MetU@{u o} CompleteSpacesU).
Proof.
  unshelve eapply (universal_arrow_from_UMP X (Incl MetU CompleteSpacesU)
                     (CompletionU X) (etaU X)).
  intros d f.
  unshelve econstructor.
  - exact (uext X (`1 d) (`2 d) f; I).
  - exact (fun a => symmetry (uext_eta X (`1 d) (`2 d) f a)).
  - intros v Hv x.
    symmetry.
    exact (uext_unique X (`1 d) (`2 d) f (`1 v) (fun a => symmetry (Hv a)) x).
Defined.

(** ** Mac Lane §IV.3: complete spaces are reflective in MetU *)

Definition CMet_Reflective_in_MetU@{u o +} :
  @Reflective MetU@{u o} CompleteSpacesU :=
  Reflective_of_UniversalArrows CMetU_Full CompletionU_UniversalArrow.

Definition completionU_adj@{u o +} :
  @reflector MetU@{u o} _ CMet_Reflective_in_MetU
    ⊣ Incl MetU@{u o} CompleteSpacesU :=
  reflective_adj CMet_Reflective_in_MetU.

Example completionU_reflector_obj@{u o +} (X : MetU@{u o}) :
  fobj[@reflector MetU@{u o} _ CMet_Reflective_in_MetU] X = CompletionU X
  := eq_refl.

Example completionU_unit_pointwise@{u o +} (X : MetU@{u o}) (a : X) :
  umap (@unit _ _ _ _ completionU_adj X) a = eta_seq X a := eq_refl.

(** ** The isometric companion: complete spaces reflective in Met *)

Definition CMet_Reflective_in_Met@{u o +} :
  @Reflective Met@{u o} CompleteSpaces :=
  Reflective_of_UniversalArrows CMet_Full
    (fun X : Met => Completion_UniversalArrow X).

Definition completion_adj@{u o +} :
  @reflector Met@{u o} _ CMet_Reflective_in_Met
    ⊣ Incl Met@{u o} CompleteSpaces :=
  reflective_adj CMet_Reflective_in_Met.

Example completion_reflector_obj@{u o +} (X : Met@{u o}) :
  fobj[@reflector Met@{u o} _ CMet_Reflective_in_Met] X = Completion_CMet X
  := eq_refl.

Example completion_unit_pointwise@{u o +} (X : Met@{u o}) (a : X) :
  isometry_map (@unit _ _ _ _ completion_adj X) a = eta_seq X a
  := eq_refl.

(* The two reflections build the same space. *)
Example completion_reflectors_agree@{u o +} (X : MetricSpace@{o}) :
  `1 (fobj[@reflector MetU@{u o} _ CMet_Reflective_in_MetU] X)
    = `1 (fobj[@reflector Met@{u o} _ CMet_Reflective_in_Met] X) := eq_refl.

(* The reflection is proper: at the harmonic space, which is not
   complete (Instance/Met.v's [Harmonic_not_MComplete]), the unit is not
   invertible.  Its inverse would send the point the embedding misses
   (Instance/Met/Completion.v's [Completion_Harmonic_adds_a_point]) to a
   point whose image is that point, and the unit applied to a point IS
   its constant sequence ([completionU_unit_pointwise]). *)
Theorem completionU_unit_Harmonic_not_iso@{u +| Set < u +} :
  IsIsomorphism
    (@unit _ _ _ _ completionU_adj (Harmonic : MetU@{u Set})) → False.
Proof.
  intros [g Hfg _].
  destruct Completion_Harmonic_adds_a_point as [z Hz].
  exact (Hz (umap g z) (Hfg z)).
Qed.
