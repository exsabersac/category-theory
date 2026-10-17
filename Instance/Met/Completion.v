Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.

Generalizable All Variables.

Open Scope R_scope.

(** * The completion of a metric space, as a universal arrow *)

(*
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Complete_metric_space#Completion
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book:      Bishop, "Foundations of Constructive Analysis", McGraw-Hill

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** A small toolkit for limits *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Un_cv_const (c : R) : Un_cv (fun _ => c) c.
Proof.
  intros eps Heps.
  exists 0%nat; intros n _.
  unfold R_dist.
  replace (c - c) with 0 by ring.
  now rewrite Rabs_R0.
Qed.

Lemma Un_cv_le_const (u : nat → R) (l c : R) (N : nat) :
  Un_cv u l → (∀ n : nat, (N <= n)%nat → u n <= c) → l <= c.
Proof.
  intros Hl Hbound.
  destruct (Rle_or_lt l c) as [Hle | Hlt]; [ exact Hle | exfalso ].
  destruct (Hl (l - c) ltac:(lra)) as [M HM].
  pose (n := Nat.max N M).
  specialize (HM n (Nat.le_max_r N M)).
  specialize (Hbound n (Nat.le_max_l N M)).
  unfold R_dist in HM.
  destruct (Rabs_def2 _ _ HM) as [_ Hlow].
  lra.
Qed.

(* A sandwich at zero: a non-negative sequence under the sum of two null
   sequences is null.  This is what makes [cs_equiv] transitive. *)
Lemma Un_cv_zero_squeeze (w u v : nat → R) :
  (∀ n, 0 <= w n) → (∀ n, w n <= u n + v n) →
  Un_cv u 0 → Un_cv v 0 → Un_cv w 0.
Proof.
  intros Hpos Hle Hu Hv eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  rewrite Rminus_0_r in *.
  pose proof (Rle_abs (u n)); pose proof (Rle_abs (v n)).
  pose proof (Hpos n); pose proof (Hle n).
  rewrite Rabs_pos_eq by exact (Hpos n).
  lra.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Un_cv_shift (u v w : nat → R) (l : R) :
  (∀ n, Rabs (u n - v n) <= w n) → Un_cv w 0 → Un_cv v l → Un_cv u l.
Proof.
  intros Hclose Hw Hv eps Heps.
  destruct (Hw (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  rewrite Rminus_0_r in H1.
  pose proof (Rle_abs (w n)) as Hwabs.
  pose proof (Hclose n) as Hcn.
  replace (u n - l) with ((u n - v n) + (v n - l)) by ring.
  eapply Rle_lt_trans; [ apply Rabs_triang |].
  lra.
Qed.

(* Limits preserve eventual ≤. *)
Lemma Un_cv_le (u v : nat → R) (a b : R) (N : nat) :
  (∀ n : nat, (N <= n)%nat → u n <= v n) → Un_cv u a → Un_cv v b → a <= b.
Proof.
  intros Hle Hu Hv.
  destruct (Rle_or_lt a b) as [H | Hlt]; [ exact H | exfalso ].
  destruct (Hu ((a - b) / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv ((a - b) / 2) ltac:(lra)) as [N2 H2].
  pose (n := Nat.max N (Nat.max N1 N2)).
  assert (N <= n)%nat as HnN by apply Nat.le_max_l.
  assert (N1 <= n)%nat as Hn1.
  { transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | apply Nat.le_max_r ]. }
  assert (N2 <= n)%nat as Hn2.
  { transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | apply Nat.le_max_r ]. }
  specialize (Hle n HnN); specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  destruct (Rabs_def2 _ _ H1) as [_ Hu'].
  destruct (Rabs_def2 _ _ H2) as [Hv' _].
  lra.
Qed.

(* Limits add. *)
Lemma Un_cv_plus (u v : nat → R) (a b : R) :
  Un_cv u a → Un_cv v b → Un_cv (fun n => u n + v n) (a + b).
Proof.
  intros Hu Hv eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  replace (u n + v n - (a + b)) with ((u n - a) + (v n - b)) by ring.
  eapply Rle_lt_trans; [ apply Rabs_triang |].
  lra.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma MConverges_dist_cv {Z : MetricSpace} (u : nat → Z) (l : Z) :
  MConverges Z u l → Un_cv (fun n => dist (u n) l) 0.
Proof.
  intros H eps Heps.
  destruct (H eps ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  unfold R_dist.
  rewrite Rminus_0_r, Rabs_pos_eq by apply dist_nonneg.
  exact (HN n Hn).
Qed.

(* Convergence only sees the sequence up to the carrier's own equality. *)
Lemma MConverges_respects_seq {Z : MetricSpace} (u v : nat → Z) (l : Z) :
  (∀ n, u n ≈ v n) → MConverges Z u l → MConverges Z v l.
Proof.
  intros Huv H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite (dist_proper (v n) (u n) l l (symmetry (Huv n)) (reflexivity l)).
  exact (HN n Hn).
Qed.

Section Completion.

(* The proofs below genuinely depend on the space being completed; [Lib.v]
   sets [Default Proof Using "Type"], which would discard it.  Same reason,
   same remedy, as Instance/Top/Interval.v and Instance/Met.v's
   [OfInjection] section. *)
Local Set Default Proof Using "All".

Context (X : MetricSpace).

(** ** Cauchy sequences as the points of the completion *)

(* A point of the completion is a sequence TOGETHER WITH its modulus, this
   library's `∃` being [sigT].  The modulus is what
   [Completion_MComplete] consumes, one per index. *)
Definition CauchySeq : Type := ∃ u : nat → X, MCauchy X u.

Definition cs_seq (x : CauchySeq) : nat → X := `1 x.
Definition cs_cauchy (x : CauchySeq) : MCauchy X (cs_seq x) := `2 x.

Definition cs_of (u : nat → X) (H : MCauchy X u) : CauchySeq := (u; H).

(* The sequence of distances between two points of the completion. *)
Definition cdist_seq (x y : CauchySeq) (n : nat) : R :=
  dist (cs_seq x n) (cs_seq y n).

Lemma cdist_seq_nonneg (x y : CauchySeq) (n : nat) : 0 <= cdist_seq x y n.
Proof. apply dist_nonneg. Qed.

(* The distances themselves form a Cauchy sequence of REALS.  This is the
   whole reason the codomain of the metric must be complete, and the
   estimate that proves it is [dist_quadrilateral]. *)
Lemma cdist_Cauchy_crit (x y : CauchySeq) : Cauchy_crit (cdist_seq x y).
Proof.
  intros eps Heps.
  destruct (cs_cauchy x (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (cs_cauchy y (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n m Hn Hm.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N1 <= m)%nat as Hm1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hm ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  assert (N2 <= m)%nat as Hm2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hm ]).
  pose proof (H1 n m Hn1 Hm1) as Hx.
  pose proof (H2 n m Hn2 Hm2) as Hy.
  unfold R_dist, cdist_seq.
  eapply Rle_lt_trans;
    [ exact (dist_quadrilateral (cs_seq x n) (cs_seq x m)
                                (cs_seq y n) (cs_seq y m)) |].
  lra.
Qed.

(** ** The distance on the completion *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cdist (x y : CauchySeq) : R :=
  proj1_sig (R_complete (cdist_seq x y) (cdist_Cauchy_crit x y)).

(* The distance IS the limit of the term-wise distances ... *)
Lemma cdist_spec (x y : CauchySeq) : Un_cv (cdist_seq x y) (cdist x y).
Proof. exact (proj2_sig (R_complete (cdist_seq x y) (cdist_Cauchy_crit x y))). Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cdist_unique (x y : CauchySeq) (r : R) :
  Un_cv (cdist_seq x y) r → cdist x y = r.
Proof.
  intro Hr.
  exact (UL_sequence (cdist_seq x y) (cdist x y) r (cdist_spec x y) Hr).
Qed.

(* Consequently the distance inherits every eventual bound. *)
Lemma cdist_le (x y : CauchySeq) (c : R) (N : nat) :
  (∀ n : nat, (N <= n)%nat → cdist_seq x y n <= c) → cdist x y <= c.
Proof. intro H; exact (Un_cv_le_const _ _ c N (cdist_spec x y) H). Qed.

Lemma cdist_nonneg (x y : CauchySeq) : 0 <= cdist x y.
Proof.
  destruct (Rle_or_lt 0 (cdist x y)) as [Hle | Hlt]; [ exact Hle | exfalso ].
  destruct (cdist_spec x y (- cdist x y) ltac:(lra)) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  unfold R_dist in HN.
  destruct (Rabs_def2 _ _ HN) as [Hhi _].
  pose proof (cdist_seq_nonneg x y N).
  lra.
Qed.

(** ** Identification of Cauchy sequences *)

(*
   本节说明 Completion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cs_equiv (x y : CauchySeq) : Prop := Un_cv (cdist_seq x y) 0.

(* Both proofs are pointwise rather than by rewriting the SEQUENCE, which
   would need functional extensionality: nothing in this development
   rewrites under a lambda. *)
Lemma cs_equiv_refl (x : CauchySeq) : cs_equiv x x.
Proof.
  intros eps Heps.
  exists 0%nat; intros n _.
  unfold R_dist, cdist_seq.
  rewrite dist_refl.
  replace (0 - 0) with 0 by ring.
  now rewrite Rabs_R0.
Qed.

Lemma cs_equiv_sym (x y : CauchySeq) : cs_equiv x y → cs_equiv y x.
Proof.
  intros H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N; intros n Hn.
  unfold R_dist, cdist_seq in *.
  rewrite (dist_sym (cs_seq y n) (cs_seq x n)).
  exact (HN n Hn).
Qed.

Lemma cs_equiv_trans (x y z : CauchySeq) :
  cs_equiv x y → cs_equiv y z → cs_equiv x z.
Proof.
  unfold cs_equiv; intros Hxy Hyz.
  apply (Un_cv_zero_squeeze _ (cdist_seq x y) (cdist_seq y z)).
  - intro n; apply cdist_seq_nonneg.
  - intro n; apply dist_triangle.
  - exact Hxy.
  - exact Hyz.
Qed.

#[export] Program Instance CauchySeq_Setoid : Setoid CauchySeq := {|
  equiv := cs_equiv
|}.
Next Obligation.
  constructor.
  - exact cs_equiv_refl.
  - exact cs_equiv_sym.
  - exact cs_equiv_trans.
Qed.

Definition CauchySeq_Object : SetoidObject :=
  {| carrier := CauchySeq; is_setoid := CauchySeq_Setoid |}.

(** ** The completion is a metric space *)

Lemma cdist_proper (x x' y y' : CauchySeq) :
  x ≈ x' → y ≈ y' → cdist x y = cdist x' y'.
Proof.
  intros Hx Hy.
  apply cdist_unique.
  (* The two distance sequences differ by at most d(xₙ,x'ₙ) + d(yₙ,y'ₙ),
     which is null; so they share a limit. *)
  apply (Un_cv_shift _ (cdist_seq x' y')
                     (fun n => cdist_seq x x' n + cdist_seq y y' n)).
  - intro n; apply dist_quadrilateral.
  - replace 0 with (0 + 0) by ring.
    exact (Un_cv_plus _ _ 0 0 Hx Hy).
  - apply cdist_spec.
Qed.

Lemma cdist_refl (x : CauchySeq) : cdist x x = 0.
Proof. exact (cdist_unique x x 0 (cs_equiv_refl x)). Qed.

Lemma cdist_separates (x y : CauchySeq) : cdist x y = 0 → x ≈ y.
Proof.
  intro H.
  unfold equiv; simpl; unfold cs_equiv.
  rewrite <- H.
  apply cdist_spec.
Qed.

Lemma cdist_sym (x y : CauchySeq) : cdist x y = cdist y x.
Proof.
  apply cdist_unique.
  apply (Un_cv_shift _ (cdist_seq y x) (fun _ => 0)).
  - intro n; unfold cdist_seq.
    rewrite (dist_sym (cs_seq x n) (cs_seq y n)).
    replace (dist (cs_seq y n) (cs_seq x n) - dist (cs_seq y n) (cs_seq x n))
      with 0 by ring.
    rewrite Rabs_R0; apply Rle_refl.
  - apply Un_cv_const.
  - apply cdist_spec.
Qed.

Lemma cdist_triangle (x y z : CauchySeq) : cdist x z <= cdist x y + cdist y z.
Proof.
  apply (Un_cv_le (cdist_seq x z)
                  (fun n => cdist_seq x y n + cdist_seq y z n) _ _ 0%nat).
  - intros n _; apply dist_triangle.
  - apply cdist_spec.
  - exact (Un_cv_plus _ _ _ _ (cdist_spec x y) (cdist_spec y z)).
Qed.

(* THE COMPLETION, as an object of [Met]. *)
Definition Completion : MetricSpace :=
  {| met_carrier    := CauchySeq_Object;
     dist           := cdist;
     dist_proper    := cdist_proper;
     dist_refl      := cdist_refl;
     dist_separates := cdist_separates;
     dist_sym       := cdist_sym;
     dist_triangle  := cdist_triangle |}.

(** ** The isometric embedding *)

Lemma const_MCauchy (a : X) : MCauchy X (fun _ => a).
Proof.
  intros eps Heps.
  exists 0%nat; intros m n _ _.
  rewrite dist_refl; exact Heps.
Qed.

Definition eta_seq (a : X) : CauchySeq := cs_of (fun _ => a) (const_MCauchy a).

(* The distance between two constant sequences is the distance of their
   values — this is where [Un_cv_const] is spent. *)
Lemma eta_dist (a b : X) : cdist (eta_seq a) (eta_seq b) = dist a b.
Proof.
  apply cdist_unique.
  (*
   本节说明 Completion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  exact (Un_cv_const (dist a b)).
Qed.

Lemma eta_proper (a b : X) : a ≈ b → eta_seq a ≈ eta_seq b.
Proof.
  intro Hab.
  apply cdist_separates.
  rewrite eta_dist.
  now apply dist_eq_zero.
Qed.

Definition eta_morphism : SetoidMorphism (met_carrier X) (met_carrier Completion).
Proof.
  unshelve refine {| morphism := eta_seq |}.
  intros a b Hab; exact (eta_proper a b Hab).
Defined.

Definition eta : Isometry X Completion :=
  {| isometry_map := eta_morphism; isometry_dist := eta_dist |}.

(* DENSITY: every point of the completion is the limit of the embedded
   terms of any Cauchy sequence naming it.  The threshold is the sequence's
   own Cauchy modulus at ε/2 — data, as always. *)
Lemma eta_dense (x : CauchySeq) :
  MConverges Completion (fun n => eta_seq (cs_seq x n)) x.
Proof.
  intros eps Heps.
  destruct (cs_cauchy x (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  (* d(η xₙ, x) = limₘ d(xₙ, xₘ) ≤ ε/2 < ε *)
  apply Rle_lt_trans with (r2 := eps / 2); [| lra ].
  apply (cdist_le _ _ _ N).
  intros m Hm.
  unfold cdist_seq; simpl.
  left; exact (HN n m Hn Hm).
Qed.

(** ** The completion is complete *)

(*
   本节说明 Completion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Complete.

Context (xi : nat → Completion).

Definition cs_pick (k : nat) : nat :=
  `1 (cs_cauchy (xi k) (harm k) (harm_pos k)).

Lemma cs_pick_spec (k : nat) (m n : nat) :
  (cs_pick k <= m)%nat → (cs_pick k <= n)%nat →
  dist (cs_seq (xi k) m) (cs_seq (xi k) n) < harm k.
Proof. exact (`2 (cs_cauchy (xi k) (harm k) (harm_pos k)) m n). Qed.

Definition cs_diag (k : nat) : X := cs_seq (xi k) (cs_pick k).

(* Each selected term names a point within 1/(k+1) of ξₖ. *)
Lemma cs_diag_close (k : nat) : cdist (eta_seq (cs_diag k)) (xi k) <= harm k.
Proof.
  apply (cdist_le _ _ _ (cs_pick k)).
  intros n Hn.
  left.
  exact (cs_pick_spec k (cs_pick k) n (Nat.le_refl _) Hn).
Qed.

Context (Hxi : MCauchy Completion xi).

Lemma cs_diag_MCauchy : MCauchy X cs_diag.
Proof.
  intros eps Heps.
  destruct (Hxi (eps / 4) ltac:(lra)) as [N2 HN2].
  (* [harm_mod (eps/4)] is written out rather than abbreviated: [lra] matches
     atoms syntactically, and a local abbreviation would hide the very term
     [harm_mod_spec] talks about. *)
  exists (Nat.max (harm_mod (eps / 4)) N2); intros j k Hj Hk.
  assert (harm_mod (eps / 4) <= j)%nat as Hj1
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_l | exact Hj ]).
  assert (harm_mod (eps / 4) <= k)%nat as Hk1
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_l | exact Hk ]).
  assert (N2 <= j)%nat as Hj2
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_r | exact Hj ]).
  assert (N2 <= k)%nat as Hk2
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_r | exact Hk ]).
  pose proof (harm_mod_spec (eps / 4) ltac:(lra)) as Hsmall.
  pose proof (harm_antitone _ _ Hj1) as Hhj.
  pose proof (harm_antitone _ _ Hk1) as Hhk.
  (* d(diag j, diag k) = cdist (η diag j) (η diag k), then two triangles *)
  rewrite <- (eta_dist (cs_diag j) (cs_diag k)).
  pose proof (cdist_triangle (eta_seq (cs_diag j)) (xi j) (eta_seq (cs_diag k)))
    as T1.
  pose proof (cdist_triangle (xi j) (xi k) (eta_seq (cs_diag k))) as T2.
  rewrite (cdist_sym (xi k) (eta_seq (cs_diag k))) in T2.
  pose proof (cs_diag_close j) as A1.
  pose proof (cs_diag_close k) as A2.
  pose proof (HN2 j k Hj2 Hk2) as Hjk.
  change (dist (xi j) (xi k)) with (cdist (xi j) (xi k)) in Hjk.
  lra.
Qed.

Definition cs_limit : Completion := cs_of cs_diag cs_diag_MCauchy.

Lemma cs_limit_spec : MConverges Completion xi cs_limit.
Proof.
  intros eps Heps.
  destruct (cs_diag_MCauchy (eps / 4) ltac:(lra)) as [M2 HM2].
  exists (Nat.max (harm_mod (eps / 4)) M2); intros k Hk.
  assert (harm_mod (eps / 4) <= k)%nat as Hk1
      by (transitivity (Nat.max (harm_mod (eps / 4)) M2);
          [ apply Nat.le_max_l | exact Hk ]).
  assert (M2 <= k)%nat as Hk2
      by (transitivity (Nat.max (harm_mod (eps / 4)) M2);
          [ apply Nat.le_max_r | exact Hk ]).
  pose proof (harm_mod_spec (eps / 4) ltac:(lra)) as Hsmall.
  pose proof (harm_antitone _ _ Hk1) as Hhk.
  (* d(ξₖ, [diag]) ≤ d(ξₖ, η diag k) + d(η diag k, [diag]) ≤ harm k + ε/4 *)
  change (cdist (xi k) cs_limit < eps).
  assert (cdist (eta_seq (cs_diag k)) cs_limit <= eps / 4) as Htail.
  { apply (cdist_le _ _ _ M2).
    intros n Hn.
    left; exact (HM2 k n Hk2 Hn). }
  pose proof (cdist_triangle (xi k) (eta_seq (cs_diag k)) cs_limit) as T.
  rewrite (cdist_sym (xi k) (eta_seq (cs_diag k))) in T.
  pose proof (cs_diag_close k) as A.
  lra.
Qed.

End Complete.

Definition Completion_MComplete : MComplete Completion :=
  fun xi Hxi => (cs_limit xi Hxi; cs_limit_spec xi Hxi).

(* The completion as an object of [CMet]. *)
Definition Completion_CMet : CMet := (Completion; Completion_MComplete).

(** ** Extending an isometry into a complete space *)

Section Extend.

Context (Y : MetricSpace).
Context (cY : MComplete Y).
Context (f : Isometry X Y).

(* The image of a Cauchy sequence under an isometry is Cauchy, with the SAME
   modulus; [cY] then names its limit. *)
Definition ext_seq (x : Completion) : nat → Y :=
  fun n => isometry_map f (cs_seq x n).

Definition ext_MCauchy (x : Completion) : MCauchy Y (ext_seq x) :=
  isometry_MCauchy f (cs_seq x) (cs_cauchy x).

Definition ext_val (x : Completion) : Y := `1 (cY (ext_seq x) (ext_MCauchy x)).

Definition ext_spec (x : Completion) : MConverges Y (ext_seq x) (ext_val x) :=
  `2 (cY (ext_seq x) (ext_MCauchy x)).

(* The term-wise distances of x and y converge to the distance of the two
   limits.  This single lemma yields both that [ext] is well defined and
   that it preserves the distance. *)
Lemma ext_dist_cv (x y : Completion) :
  Un_cv (cdist_seq x y) (dist (ext_val x) (ext_val y)).
Proof.
  apply (Un_cv_shift _ (fun _ => dist (ext_val x) (ext_val y))
           (fun n => dist (ext_seq x n) (ext_val x)
                     + dist (ext_seq y n) (ext_val y))).
  - intro n.
    unfold cdist_seq.
    rewrite <- (isometry_dist f (cs_seq x n) (cs_seq y n)).
    exact (dist_quadrilateral (ext_seq x n) (ext_val x)
                              (ext_seq y n) (ext_val y)).
  - replace 0 with (0 + 0) by ring.
    exact (Un_cv_plus _ _ 0 0
             (MConverges_dist_cv (ext_seq x) (ext_val x) (ext_spec x))
             (MConverges_dist_cv (ext_seq y) (ext_val y) (ext_spec y))).
  - apply Un_cv_const.
Qed.

Lemma ext_isometry (x y : Completion) :
  dist (ext_val x) (ext_val y) = cdist x y.
Proof. symmetry; exact (cdist_unique x y _ (ext_dist_cv x y)). Qed.

Lemma ext_proper (x y : Completion) : x ≈ y → ext_val x ≈ ext_val y.
Proof.
  intro Hxy.
  apply dist_separates.
  rewrite ext_isometry.
  exact (cdist_unique x y 0 Hxy).
Qed.

Definition ext_morphism : SetoidMorphism (met_carrier Completion) (met_carrier Y).
Proof.
  unshelve refine {| morphism := ext_val |}.
  intros x y Hxy; exact (ext_proper x y Hxy).
Defined.

Definition ext : Isometry Completion Y :=
  {| isometry_map := ext_morphism; isometry_dist := ext_isometry |}.

(* THE TRIANGLE: the extension restricted along the embedding is the
   original isometry.  The image sequence is constant at [f a], so its limit
   is [f a]. *)
Lemma ext_eta (a : X) : ext_val (eta_seq a) ≈ isometry_map f a.
Proof.
  apply (MConverges_unique (ext_seq (eta_seq a))).
  - exact (ext_spec (eta_seq a)).
  - intros eps Heps.
    exists 0%nat; intros n _.
    rewrite dist_refl; exact Heps.
Qed.

(* UNIQUENESS: any isometry out of the completion that restricts to [f]
   along the embedding IS [ext].  Density does the work — the two maps agree
   on a dense set and both preserve limits. *)
Lemma ext_unique (g : Isometry Completion Y) :
  (∀ a : X, isometry_map g (eta_seq a) ≈ isometry_map f a) →
  ∀ x : Completion, isometry_map g x ≈ ext_val x.
Proof.
  intros Hg x.
  apply (MConverges_unique (ext_seq x)).
  - (* g carries the embedded terms to the image sequence, and preserves
       the limit of the dense approximation *)
    apply (MConverges_respects_seq
             (fun n => isometry_map g (eta_seq (cs_seq x n))) (ext_seq x)).
    + intro n; exact (Hg (cs_seq x n)).
    + exact (isometry_MConverges g _ x (eta_dense x)).
  - exact (ext_spec x).
Qed.

End Extend.

(** ** The universal arrow *)

(* Mac Lane §III.1's sentence, in the direct encoding of
   Theory/Universal/Arrow.v: the embedding is a universal arrow from X to
   the inclusion of the complete spaces. *)
Definition Completion_AUniversalArrow :
  AUniversalArrow (X : Met) CMet_Incl Completion_CMet.
Proof.
  unshelve econstructor.
  - exact eta.
  - intros d f.
    unshelve econstructor.
    + exact (ext (`1 d) (`2 d) f; I).
    + exact (fun a => ext_eta (`1 d) (`2 d) f a).
    + intros v Hv x.
      symmetry.
      exact (ext_unique (`1 d) (`2 d) f (`1 v) Hv x).
Defined.

(* The same statement in the comma-category encoding, which is what
   [ump_universal_arrows] and the [LeftAdjointFunctorFromUniversalArrows]
   machinery consume. *)
Definition Completion_UniversalArrow : UniversalArrow (X : Met) CMet_Incl.
Proof.
  unshelve eapply (universal_arrow_from_UMP (X : Met) CMet_Incl Completion_CMet eta).
  intros d f.
  unshelve econstructor.
  - exact (ext (`1 d) (`2 d) f; I).
  - exact (fun a => symmetry (ext_eta (`1 d) (`2 d) f a)).
  - intros v Hv x.
    symmetry.
    exact (ext_unique (`1 d) (`2 d) f (`1 v) (fun a => symmetry (Hv a)) x).
Defined.

End Completion.

(** ** Uniqueness of the completion *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary completion_unique (X : MetricSpace) (Z : CMet)
      (U : AUniversalArrow (X : Met) CMet_Incl Z) :
  ∃! i : Completion_CMet X ≅[CMet] Z,
    fmap[CMet_Incl] i ∘ eta X ≈ @universal_arrow _ _ (X : Met) CMet_Incl Z U.
Proof. exact (auniversal_arrow_unique (Completion_AUniversalArrow X) U). Qed.

(* The same statement with neither solution privileged: any two complete
   spaces solving X's completion problem are uniquely compatibly
   isomorphic. *)
Corollary completions_unique (X : MetricSpace) (A B : CMet)
      (U1 : AUniversalArrow (X : Met) CMet_Incl A)
      (U2 : AUniversalArrow (X : Met) CMet_Incl B) :
  ∃! i : A ≅[CMet] B,
    fmap[CMet_Incl] i ∘ @universal_arrow _ _ (X : Met) CMet_Incl A U1
      ≈ @universal_arrow _ _ (X : Met) CMet_Incl B U2.
Proof. exact (auniversal_arrow_unique U1 U2). Qed.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Non-vacuity: a completion that genuinely adds a point *)

(*
   本节说明 Completion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition harm_point : Completion Harmonic :=
  cs_of Harmonic (fun n => n) harm_seq_MCauchy.

Theorem eta_Harmonic_not_surjective (k : Harmonic) :
  isometry_map (eta Harmonic) k ≈ harm_point → False.
Proof.
  intro H.
  pose proof (harm_pos k) as Hk.
  destruct (H (harm k / 2) ltac:(lra)) as [N HN].
  pose (n := Nat.max N (2 * k + 1)).
  specialize (HN n (Nat.le_max_l N (2 * k + 1))).
  (* the n-th term of the distance sequence is |harm k - harm n| *)
  change (R_dist (Rabs (harm k - harm n)) 0 < harm k / 2) in HN.
  unfold R_dist in HN.
  rewrite Rminus_0_r, Rabs_pos_eq in HN by apply Rabs_pos.
  pose proof (harm_half k n (Nat.le_max_r N (2 * k + 1))) as Hsmall.
  pose proof (harm_pos n).
  rewrite Rabs_pos_eq in HN by lra.
  lra.
Qed.

(*
   本节说明 Completion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Completion_Harmonic_adds_a_point :
  ∃ z : Completion Harmonic,
    ∀ k : Harmonic, isometry_map (eta Harmonic) k ≈ z → False.
Proof. exact (harm_point; eta_Harmonic_not_surjective). Qed.
