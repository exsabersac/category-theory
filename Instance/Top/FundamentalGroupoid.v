Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Bool.Bool.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Structure.Groupoid.Basepoint.

Generalizable All Variables.

Open Scope R_scope.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(** * The fundamental groupoid of a topological space *)

(*
   nLab:      https://ncatlab.org/nlab/show/fundamental+groupoid
   nLab:      https://ncatlab.org/nlab/show/fundamental+group
   Wikipedia: https://en.wikipedia.org/wiki/Fundamental_groupoid
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Riehl, "Category Theory in Context", Example 1.1.13(ii),
   Paper:     Brown, "From groups to groupoids: a brief survey", Bulletin of

   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Paths *)

(* A path from a to b: a continuous map out of the interval with the two
   endpoint conditions, stated up to `≈` in the space's own equality. *)
Record Path (X : TopSpace) (a b : X) := {
  path_map :> I_Top ~{Top}~> X;

  path_src : path_map I_zero ≈ a;
  path_tgt : path_map I_one ≈ b
}.

Arguments path_map {X a b} _.
Arguments path_src {X a b} _.
Arguments path_tgt {X a b} _.

(** ** Homotopy rel endpoints *)

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record ArrowHomotopy {X : TopSpace} (a b : X) (p q : I_Top ~{Top}~> X) := {
  ah_map :> Sq_Top ~{Top}~> X;

  ah_bot : ∀ t : Ipt, ah_map (sq_pt t I_zero) ≈ p t;
  ah_top : ∀ t : Ipt, ah_map (sq_pt t I_one) ≈ q t;
  ah_left : ∀ s : Ipt, ah_map (sq_pt I_zero s) ≈ a;
  ah_right : ∀ s : Ipt, ah_map (sq_pt I_one s) ≈ b
}.

Arguments ah_map {X a b p q} _.
Arguments ah_bot {X a b p q} _ _.
Arguments ah_top {X a b p q} _ _.
Arguments ah_left {X a b p q} _ _.
Arguments ah_right {X a b p q} _ _.

(* Homotopy of PATHS is homotopy of their underlying arrows. *)
Definition PathHomotopy {X : TopSpace} {a b : X} (p q : Path X a b) : Type :=
  ArrowHomotopy a b (path_map p) (path_map q).

(** ** Evaluating composites *)

(* Two rewriting lemmas used throughout: a composite arrow evaluates by
   evaluating the inner one first, and the outer arrow only sees coordinates. *)
Lemma comp_eval_I {X : TopSpace} (f : I_Top ~{Top}~> X)
      (g : I_Top ~{Top}~> I_Top) (x y : Ipt) :
  ival (g x) = ival y → (f ∘[Top] g) x ≈ f y.
Proof. intro H; exact (Iap f (g x) y H). Qed.

Lemma comp_eval_Sq {X : TopSpace} (f : I_Top ~{Top}~> X)
      (g : Sq_Top ~{Top}~> I_Top) (z : BS_Sq) (y : Ipt) :
  ival (g z) = ival y → (f ∘[Top] g) z ≈ f y.
Proof. intro H; exact (Iap f (g z) y H). Qed.

Lemma comp_eval_SqSq {X : TopSpace} (F : Sq_Top ~{Top}~> X)
      (G : Sq_Top ~{Top}~> Sq_Top) (z w : BS_Sq) :
  sq_t (G z) = sq_t w → sq_s (G z) = sq_s w → (F ∘[Top] G) z ≈ F w.
Proof. intros H1 H2; exact (Sqap F (G z) w H1 H2). Qed.

(** ** Homotopy is an equivalence relation *)

(* Reflexivity: the homotopy constant in the second coordinate. *)
Definition ah_refl {X : TopSpace} (a b : X) (p : I_Top ~{Top}~> X)
           (Ha : p I_zero ≈ a) (Hb : p I_one ≈ b) : ArrowHomotopy a b p p.
Proof.
  refine {| ah_map := p ∘[Top] Sq_first |}.
  - intro t; apply comp_eval_Sq; reflexivity.
  - intro t; apply comp_eval_Sq; reflexivity.
  - intro s.
    transitivity (p I_zero); [ | exact Ha ].
    apply comp_eval_Sq; reflexivity.
  - intro s.
    transitivity (p I_one); [ | exact Hb ].
    apply comp_eval_Sq; reflexivity.
Defined.

(* Symmetry: turn the square upside down. *)
Definition ah_sym {X : TopSpace} {a b : X} {p q : I_Top ~{Top}~> X}
           (H : ArrowHomotopy a b p q) : ArrowHomotopy a b q p.
Proof.
  refine {| ah_map := ah_map H ∘[Top] Sq_flip |}.
  - intro t.
    transitivity (ah_map H (sq_pt t I_one)); [ | exact (ah_top H t) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, ival_I_zero, ival_I_one; lra.
  - intro t.
    transitivity (ah_map H (sq_pt t I_zero)); [ | exact (ah_bot H t) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, ival_I_zero, ival_I_one; lra.
  - intro s.
    transitivity (ah_map H (sq_pt I_zero (I_rev s))); [ | exact (ah_left H _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, I_rev_eval; reflexivity.
  - intro s.
    transitivity (ah_map H (sq_pt I_one (I_rev s))); [ | exact (ah_right H _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, I_rev_eval; reflexivity.
Defined.

(* Transitivity: stack the two squares, each run at double speed vertically.
   This is [paste_arrow] applied along the second coordinate of the square. *)
Section HomotopyTrans.

Context {X : TopSpace}.
Context {a b : X}.
Context {p q r : I_Top ~{Top}~> X}.
Context (H1 : ArrowHomotopy a b p q).
Context (H2 : ArrowHomotopy a b q r).

Lemma ah_trans_agree (z : BS_Sq) : sq_s z = 1/2 →
  (ah_map H1 ∘[Top] Sq_lower) z ≈ (ah_map H2 ∘[Top] Sq_upper) z.
Proof.
  intro Hz.
  transitivity (q (bs_fst z)).
  - transitivity (ah_map H1 (sq_pt (bs_fst z) I_one)).
    + apply comp_eval_SqSq.
      * rewrite Sq_lower_t, sq_pt_t; reflexivity.
      * rewrite Sq_lower_s, sq_pt_s, ival_I_one, Hz; Rlin.
    + exact (ah_top H1 (bs_fst z)).
  - symmetry.
    transitivity (ah_map H2 (sq_pt (bs_fst z) I_zero)).
    + apply comp_eval_SqSq.
      * rewrite Sq_upper_t, sq_pt_t; reflexivity.
      * rewrite Sq_upper_s, sq_pt_s, ival_I_zero, Hz; Rlin.
    + exact (ah_bot H2 (bs_fst z)).
Qed.

Definition ah_trans_map : Sq_Top ~{Top}~> X :=
  paste_arrow (A:=BS_Sq) sq_s Sq_s_lip (1/2)
    (ah_map H1 ∘[Top] Sq_lower) (ah_map H2 ∘[Top] Sq_upper) ah_trans_agree.

Lemma ah_trans_lower (z : BS_Sq) :
  sq_s z <= 1/2 → ah_trans_map z ≈ (ah_map H1 ∘[Top] Sq_lower) z.
Proof.
  exact (paste_left (A:=BS_Sq) sq_s Sq_s_lip (1/2) _ _ ah_trans_agree z).
Qed.

Lemma ah_trans_upper (z : BS_Sq) :
  1/2 <= sq_s z → ah_trans_map z ≈ (ah_map H2 ∘[Top] Sq_upper) z.
Proof.
  exact (paste_right (A:=BS_Sq) sq_s Sq_s_lip (1/2) _ _ ah_trans_agree z).
Qed.

Definition ah_trans : ArrowHomotopy a b p r.
Proof.
  refine {| ah_map := ah_trans_map |}.
  - intro t.
    transitivity ((ah_map H1 ∘[Top] Sq_lower) (sq_pt t I_zero)).
    + apply ah_trans_lower; rewrite sq_pt_s, ival_I_zero; lra.
    + transitivity (ah_map H1 (sq_pt t I_zero)); [ | exact (ah_bot H1 t) ].
      apply comp_eval_SqSq.
      * rewrite Sq_lower_t; reflexivity.
      * rewrite Sq_lower_s, !sq_pt_s, ival_I_zero; Rlin.
  - intro t.
    transitivity ((ah_map H2 ∘[Top] Sq_upper) (sq_pt t I_one)).
    + apply ah_trans_upper; rewrite sq_pt_s, ival_I_one; lra.
    + transitivity (ah_map H2 (sq_pt t I_one)); [ | exact (ah_top H2 t) ].
      apply comp_eval_SqSq.
      * rewrite Sq_upper_t; reflexivity.
      * rewrite Sq_upper_s, !sq_pt_s, ival_I_one; Rlin.
  - intro s.
    destruct (Rle_dec (ival s) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_lower) (sq_pt I_zero s)).
      * apply ah_trans_lower; rewrite sq_pt_s; exact Hle.
      * transitivity (ah_map H1 (sq_pt I_zero (I_dbl s)));
          [ | exact (ah_left H1 (I_dbl s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_lower_t; reflexivity. }
        { rewrite Sq_lower_s, !sq_pt_s, I_dbl_eval; reflexivity. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_upper) (sq_pt I_zero s)).
      * apply ah_trans_upper; rewrite sq_pt_s; lra.
      * transitivity (ah_map H2 (sq_pt I_zero (I_dbl' s)));
          [ | exact (ah_left H2 (I_dbl' s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_upper_t; reflexivity. }
        { rewrite Sq_upper_s, !sq_pt_s, I_dbl'_eval; reflexivity. }
  - intro s.
    destruct (Rle_dec (ival s) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_lower) (sq_pt I_one s)).
      * apply ah_trans_lower; rewrite sq_pt_s; exact Hle.
      * transitivity (ah_map H1 (sq_pt I_one (I_dbl s)));
          [ | exact (ah_right H1 (I_dbl s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_lower_t; reflexivity. }
        { rewrite Sq_lower_s, !sq_pt_s, I_dbl_eval; reflexivity. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_upper) (sq_pt I_one s)).
      * apply ah_trans_upper; rewrite sq_pt_s; lra.
      * transitivity (ah_map H2 (sq_pt I_one (I_dbl' s)));
          [ | exact (ah_right H2 (I_dbl' s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_upper_t; reflexivity. }
        { rewrite Sq_upper_s, !sq_pt_s, I_dbl'_eval; reflexivity. }
Defined.

End HomotopyTrans.

(* Homotopy also transports along pointwise `≈`-equality of the arrows
   themselves, which is what lets a computation that changes a path only up
   to the hom-setoid of Top be applied inside a homotopy class. *)
Definition ah_pointwise {X : TopSpace} {a b : X} {p q p' q' : I_Top ~{Top}~> X}
           (Hp : p ≈ p') (Hq : q ≈ q') (H : ArrowHomotopy a b p q) :
  ArrowHomotopy a b p' q'.
Proof.
  refine {| ah_map := ah_map H |}.
  - intro t; rewrite (ah_bot H t); exact (Hp t).
  - intro t; rewrite (ah_top H t); exact (Hq t).
  - exact (ah_left H).
  - exact (ah_right H).
Defined.

(** ** Constant paths, reversal, and concatenation *)

Definition const_arrow {X : TopSpace} (a : X) : I_Top ~{Top}~> X :=
  Build_ContinuousMorphism I_Top X
    (const_morphism (top_carrier I_Top) (top_carrier X) a)
    (fun U _ => open_const I_Top (U a)).

Lemma const_arrow_eval {X : TopSpace} (a : X) (x : Ipt) : const_arrow a x ≈ a.
Proof. reflexivity. Qed.

Definition const_path {X : TopSpace} (a : X) : Path X a a := {|
  path_map := const_arrow a;
  path_src := reflexivity a;
  path_tgt := reflexivity a
|}.

Lemma path_rev_src {X : TopSpace} {a b : X} (p : Path X a b) :
  (path_map p ∘[Top] I_rev) I_zero ≈ b.
Proof.
  transitivity (path_map p I_one); [ | exact (path_tgt p) ].
  apply comp_eval_I; rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
Qed.

Lemma path_rev_tgt {X : TopSpace} {a b : X} (p : Path X a b) :
  (path_map p ∘[Top] I_rev) I_one ≈ a.
Proof.
  transitivity (path_map p I_zero); [ | exact (path_src p) ].
  apply comp_eval_I; rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
Qed.

Definition path_rev {X : TopSpace} {a b : X} (p : Path X a b) : Path X b a := {|
  path_map := path_map p ∘[Top] I_rev;
  path_src := path_rev_src p;
  path_tgt := path_rev_tgt p
|}.

Section Concat.

Context {X : TopSpace}.
Context (b : X).
Context (p q : I_Top ~{Top}~> X).
Context (Hp : p I_one ≈ b).
Context (Hq : q I_zero ≈ b).

Lemma concat_agree (x : BS_I) : ival x = 1/2 →
  (p ∘[Top] I_dbl) x ≈ (q ∘[Top] I_dbl') x.
Proof.
  intro Hx.
  transitivity b.
  - transitivity (p I_one); [ | exact Hp ].
    apply comp_eval_I.
    rewrite I_dbl_eval, ival_I_one, Hx; Rlin.
  - symmetry.
    transitivity (q I_zero); [ | exact Hq ].
    apply comp_eval_I.
    rewrite I_dbl'_eval, ival_I_zero, Hx; Rlin.
Qed.

(* The reparametrized concatenation: p run at double speed on the first half
   of the interval, q on the second. *)
Definition concat_arrow : I_Top ~{Top}~> X :=
  paste_arrow (A:=BS_I) ival I_coord_lip (1/2)
    (p ∘[Top] I_dbl) (q ∘[Top] I_dbl') concat_agree.

Lemma concat_first (x y : Ipt) :
  ival x <= 1/2 → ival y = 2 * ival x → concat_arrow x ≈ p y.
Proof.
  intros H1 H2.
  transitivity ((p ∘[Top] I_dbl) x).
  - exact (paste_left (A:=BS_I) ival I_coord_lip (1/2) _ _ concat_agree x H1).
  - apply comp_eval_I.
    rewrite I_dbl_eval, H2; Rlin.
Qed.

Lemma concat_second (x y : Ipt) :
  1/2 <= ival x → ival y = 2 * ival x - 1 → concat_arrow x ≈ q y.
Proof.
  intros H1 H2.
  transitivity ((q ∘[Top] I_dbl') x).
  - exact (paste_right (A:=BS_I) ival I_coord_lip (1/2) _ _ concat_agree x H1).
  - apply comp_eval_I.
    rewrite I_dbl'_eval, H2; Rlin.
Qed.

Lemma concat_src (a : X) (Ha : p I_zero ≈ a) : concat_arrow I_zero ≈ a.
Proof.
  transitivity (p I_zero); [ | exact Ha ].
  apply (concat_first I_zero I_zero); rewrite ival_I_zero; lra.
Qed.

Lemma concat_tgt (c : X) (Hc : q I_one ≈ c) : concat_arrow I_one ≈ c.
Proof.
  transitivity (q I_one); [ | exact Hc ].
  apply (concat_second I_one I_one); rewrite ival_I_one; lra.
Qed.

End Concat.

Definition path_concat {X : TopSpace} {a b c : X}
           (p : Path X a b) (q : Path X b c) : Path X a c := {|
  path_map := concat_arrow b (path_map p) (path_map q) (path_tgt p) (path_src q);
  path_src := concat_src b (path_map p) (path_map q) (path_tgt p) (path_src q)
                a (path_src p);
  path_tgt := concat_tgt b (path_map p) (path_map q) (path_tgt p) (path_src q)
                c (path_tgt q)
|}.

(** ** The straight-line homotopy of parameters *)

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Straight.

Context {X : TopSpace}.
Context (a b : X).
Context (p : I_Top ~{Top}~> X).
Context (phi psi : R → R).
Context (Hphi0 : ∀ t, 0 <= t → t <= 1 → 0 <= phi t).
Context (Hphi1 : ∀ t, 0 <= t → t <= 1 → phi t <= 1).
Context (Hpsi0 : ∀ t, 0 <= t → t <= 1 → 0 <= psi t).
Context (Hpsi1 : ∀ t, 0 <= t → t <= 1 → psi t <= 1).
Context (Hphil : RLip 2 phi).
Context (Hpsil : RLip 2 psi).
Context (He0 : phi 0 = psi 0).
Context (He1 : phi 1 = psi 1).
Context (Hva : ∀ y : Ipt, ival y = phi 0 → p y ≈ a).
Context (Hvb : ∀ y : Ipt, ival y = phi 1 → p y ≈ b).
Context (u v : I_Top ~{Top}~> X).
Context (Hu : ∀ x y : Ipt, ival y = phi (ival x) → u x ≈ p y).
Context (Hv : ∀ x y : Ipt, ival y = psi (ival x) → v x ≈ p y).

Definition straight_map : Sq_Top ~{Top}~> I_Top :=
  Sq_hmap phi psi 2 two_pos Hphi0 Hphi1 Hpsi0 Hpsi1 Hphil Hpsil.

Definition straight_homotopy : ArrowHomotopy a b u v.
Proof.
  refine {| ah_map := p ∘[Top] straight_map |}.
  - intro t.
    assert (Heq : ival (straight_map (sq_pt t I_zero)) = phi (ival t)).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_zero; ring. }
    symmetry.
    exact (Hu t (straight_map (sq_pt t I_zero)) Heq).
  - intro t.
    assert (Heq : ival (straight_map (sq_pt t I_one)) = psi (ival t)).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_one; ring. }
    symmetry.
    exact (Hv t (straight_map (sq_pt t I_one)) Heq).
  - intro s.
    assert (Heq : ival (straight_map (sq_pt I_zero s)) = phi 0).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_zero, <- He0; ring. }
    exact (Hva (straight_map (sq_pt I_zero s)) Heq).
  - intro s.
    assert (Heq : ival (straight_map (sq_pt I_one s)) = phi 1).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_one, <- He1; ring. }
    exact (Hvb (straight_map (sq_pt I_one s)) Heq).
Defined.

End Straight.

(** ** Evaluating a concatenation of paths *)

Lemma path_at_zero {X : TopSpace} {a b : X} (p : Path X a b) (y : Ipt) :
  ival y = 0 → path_map p y ≈ a.
Proof.
  intro H.
  transitivity (path_map p I_zero); [ | exact (path_src p) ].
  apply Iap; rewrite H, ival_I_zero; reflexivity.
Qed.

Lemma path_at_one {X : TopSpace} {a b : X} (p : Path X a b) (y : Ipt) :
  ival y = 1 → path_map p y ≈ b.
Proof.
  intro H.
  transitivity (path_map p I_one); [ | exact (path_tgt p) ].
  apply Iap; rewrite H, ival_I_one; reflexivity.
Qed.

Lemma path_concat_first {X : TopSpace} {a b c : X}
      (p : Path X a b) (q : Path X b c) (x y : Ipt) :
  ival x <= 1/2 → ival y = 2 * ival x →
  path_map (path_concat p q) x ≈ path_map p y.
Proof. apply concat_first. Qed.

Lemma path_concat_second {X : TopSpace} {a b c : X}
      (p : Path X a b) (q : Path X b c) (x y : Ipt) :
  1/2 <= ival x → ival y = 2 * ival x - 1 →
  path_map (path_concat p q) x ≈ path_map q y.
Proof. apply concat_second. Qed.

(** ** The three category laws, pointwise *)

(* Right unit: p followed by the constant path at b agrees pointwise with p
   reparametrized by [rf_dbl]. *)
Lemma unit_right_pointwise {X : TopSpace} {a b : X} (p : Path X a b) (x y : Ipt) :
  ival y = rf_dbl (ival x) →
  path_map (path_concat p (const_path b)) x ≈ path_map p y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - apply path_concat_first; [ exact Hle | ].
    rewrite Hy; unfold rf_dbl; Rlin.
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (const_path b)
                    (mkI (2 * ival x - 1) ltac:(lra) ltac:(lra))).
    + apply path_concat_second; simpl; lra.
    + transitivity b.
      * exact (const_arrow_eval b _).
      * symmetry; apply (path_at_one p).
        rewrite Hy; unfold rf_dbl; Rlin.
Qed.

(* Left unit: the constant path at a followed by p agrees pointwise with p
   reparametrized by [rf_dbl']. *)
Lemma unit_left_pointwise {X : TopSpace} {a b : X} (p : Path X a b) (x y : Ipt) :
  ival y = rf_dbl' (ival x) →
  path_map (path_concat (const_path a) p) x ≈ path_map p y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - transitivity (path_map (const_path a)
                    (mkI (2 * ival x) ltac:(lra) ltac:(lra))).
    + apply path_concat_first; simpl; lra.
    + transitivity a.
      * exact (const_arrow_eval a _).
      * symmetry; apply (path_at_zero p).
        rewrite Hy; unfold rf_dbl'; Rlin.
  - apply Rnot_le_lt in Hnle.
    apply path_concat_second; [ lra | ].
    rewrite Hy; unfold rf_dbl'; Rlin.
Qed.

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma assoc_pointwise {X : TopSpace} {a b c d : X}
      (p : Path X a b) (q : Path X b c) (r : Path X c d) (x y : Ipt) :
  ival y = rf_assoc (ival x) →
  path_map (path_concat (path_concat p q) r) x
    ≈ path_map (path_concat p (path_concat q r)) y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/4)) as [Hc1 | Hn1].
  - (* first quarter: both sides run p at quadruple speed *)
    rewrite rf_assoc_first in Hy by lra.
    transitivity (path_map p (mkI (4 * ival x) ltac:(lra) ltac:(lra))).
    + transitivity (path_map (path_concat p q)
                      (mkI (2 * ival x) ltac:(lra) ltac:(lra))).
      * apply path_concat_first; simpl; lra.
      * apply path_concat_first; simpl; lra.
    + symmetry; apply path_concat_first; simpl; lra.
  - apply Rnot_le_lt in Hn1.
    destruct (Rle_dec (ival x) (1/2)) as [Hc2 | Hn2].
    + (* second quarter: both sides run q *)
      rewrite rf_assoc_middle in Hy by lra.
      transitivity (path_map q (mkI (4 * ival x - 1) ltac:(lra) ltac:(lra))).
      * transitivity (path_map (path_concat p q)
                        (mkI (2 * ival x) ltac:(lra) ltac:(lra))).
        { apply path_concat_first; simpl; lra. }
        { apply path_concat_second; simpl; lra. }
      * symmetry.
        transitivity (path_map (path_concat q r)
                        (mkI (2 * ival x - 1/2) ltac:(lra) ltac:(lra))).
        { apply path_concat_second; simpl; lra. }
        { apply path_concat_first; simpl; lra. }
    + (* second half: both sides run r *)
      apply Rnot_le_lt in Hn2.
      rewrite rf_assoc_last in Hy by lra.
      transitivity (path_map r (mkI (2 * ival x - 1) ltac:(lra) ltac:(lra))).
      * apply path_concat_second; simpl; lra.
      * symmetry.
        transitivity (path_map (path_concat q r)
                        (mkI (ival x) ltac:(lra) ltac:(lra))).
        { apply path_concat_second; simpl; lra. }
        { apply path_concat_second; simpl; lra. }
Qed.

(* Inversion: a path followed by its reverse agrees pointwise with the path
   reparametrized by the tent map, which goes out and comes back. *)
Lemma inverse_pointwise {X : TopSpace} {a b : X} (p : Path X a b) (x y : Ipt) :
  ival y = rf_tent (ival x) →
  path_map (path_concat p (path_rev p)) x ≈ path_map p y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - apply path_concat_first; [ exact Hle | ].
    rewrite Hy; unfold rf_tent; Rlin.
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (path_rev p)
                    (mkI (2 * ival x - 1) ltac:(lra) ltac:(lra))).
    + apply path_concat_second; simpl; lra.
    + apply comp_eval_I.
      rewrite I_rev_eval, Hy; simpl; unfold rf_tent; Rlin.
Qed.

(** ** The four laws as homotopies *)

Lemma unit_right_homotopy {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat p (const_path b)) p.
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a b (path_map p) rf_dbl rf_id
            rf_dbl_lo rf_dbl_hi rf_id_lo rf_id_hi rf_dbl_lip rf_id_lip
            _ _ _ _ _ _ _ _).
  - exact rf_dbl_zero.
  - exact rf_dbl_one.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_dbl_zero.
  - intros y Hy; apply (path_at_one p); rewrite Hy; exact rf_dbl_one.
  - exact (unit_right_pointwise p).
  - intros x y Hy; apply Iap; symmetry; exact Hy.
Defined.

Lemma unit_left_homotopy {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat (const_path a) p) p.
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a b (path_map p) rf_dbl' rf_id
            rf_dbl'_lo rf_dbl'_hi rf_id_lo rf_id_hi rf_dbl'_lip rf_id_lip
            _ _ _ _ _ _ _ _).
  - exact rf_dbl'_zero.
  - exact rf_dbl'_one.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_dbl'_zero.
  - intros y Hy; apply (path_at_one p); rewrite Hy; exact rf_dbl'_one.
  - exact (unit_left_pointwise p).
  - intros x y Hy; apply Iap; symmetry; exact Hy.
Defined.

Lemma assoc_homotopy {X : TopSpace} {a b c d : X}
      (p : Path X a b) (q : Path X b c) (r : Path X c d) :
  PathHomotopy (path_concat (path_concat p q) r)
               (path_concat p (path_concat q r)).
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a d
            (path_map (path_concat p (path_concat q r))) rf_assoc rf_id
            rf_assoc_lo rf_assoc_hi rf_id_lo rf_id_hi rf_assoc_lip rf_id_lip
            _ _ _ _ _ _ _ _).
  - exact rf_assoc_zero.
  - exact rf_assoc_one.
  - intros y Hy; apply (path_at_zero (path_concat p (path_concat q r)));
      rewrite Hy; exact rf_assoc_zero.
  - intros y Hy; apply (path_at_one (path_concat p (path_concat q r)));
      rewrite Hy; exact rf_assoc_one.
  - exact (assoc_pointwise p q r).
  - intros x y Hy; apply Iap; symmetry; exact Hy.
Defined.

Lemma inverse_homotopy {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat p (path_rev p)) (const_path a).
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a a (path_map p) rf_tent rf_zero
            rf_tent_lo rf_tent_hi rf_zero_lo rf_zero_hi rf_tent_lip rf_zero_lip
            _ _ _ _ _ _ _ _).
  - exact rf_tent_zero.
  - exact rf_tent_one.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_tent_zero.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_tent_one.
  - exact (inverse_pointwise p).
  - intros x y Hy.
    transitivity a.
    + exact (const_arrow_eval a x).
    + symmetry; apply (path_at_zero p); exact Hy.
Defined.

(** ** Concatenation is well defined on homotopy classes *)

Section HomotopyConcat.

Context {X : TopSpace}.
Context {a b c : X}.
Context {p p' q q' : I_Top ~{Top}~> X}.
Context (H1 : ArrowHomotopy a b p p').
Context (H2 : ArrowHomotopy b c q q').
Context (Hp : p I_one ≈ b) (Hq : q I_zero ≈ b).
Context (Hp' : p' I_one ≈ b) (Hq' : q' I_zero ≈ b).

Lemma hconcat_agree (z : BS_Sq) : sq_t z = 1/2 →
  (ah_map H1 ∘[Top] Sq_leftside) z ≈ (ah_map H2 ∘[Top] Sq_rightside) z.
Proof.
  intro Hz.
  transitivity b.
  - transitivity (ah_map H1 (sq_pt I_one (bs_snd z))); [ | exact (ah_right H1 _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_leftside_t, sq_pt_t, ival_I_one, Hz; Rlin.
    + rewrite Sq_leftside_s, sq_pt_s; reflexivity.
  - symmetry.
    transitivity (ah_map H2 (sq_pt I_zero (bs_snd z))); [ | exact (ah_left H2 _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_rightside_t, sq_pt_t, ival_I_zero, Hz; Rlin.
    + rewrite Sq_rightside_s, sq_pt_s; reflexivity.
Qed.

Definition hconcat_map : Sq_Top ~{Top}~> X :=
  paste_arrow (A:=BS_Sq) sq_t Sq_t_lip (1/2)
    (ah_map H1 ∘[Top] Sq_leftside) (ah_map H2 ∘[Top] Sq_rightside) hconcat_agree.

Lemma hconcat_left (z : BS_Sq) :
  sq_t z <= 1/2 → hconcat_map z ≈ (ah_map H1 ∘[Top] Sq_leftside) z.
Proof.
  exact (paste_left (A:=BS_Sq) sq_t Sq_t_lip (1/2) _ _ hconcat_agree z).
Qed.

Lemma hconcat_right (z : BS_Sq) :
  1/2 <= sq_t z → hconcat_map z ≈ (ah_map H2 ∘[Top] Sq_rightside) z.
Proof.
  exact (paste_right (A:=BS_Sq) sq_t Sq_t_lip (1/2) _ _ hconcat_agree z).
Qed.

Definition hconcat :
  ArrowHomotopy a c (concat_arrow b p q Hp Hq) (concat_arrow b p' q' Hp' Hq').
Proof.
  refine {| ah_map := hconcat_map |}.
  - intro t.
    destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_leftside) (sq_pt t I_zero)).
      * apply hconcat_left; rewrite sq_pt_t; exact Hle.
      * transitivity (ah_map H1 (sq_pt (I_dbl t) I_zero)).
        { apply comp_eval_SqSq.
          - rewrite Sq_leftside_t, !sq_pt_t, I_dbl_eval; reflexivity.
          - rewrite Sq_leftside_s, !sq_pt_s; reflexivity. }
        { transitivity (p (I_dbl t)); [ exact (ah_bot H1 (I_dbl t)) | ].
          symmetry.
          apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ]. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_rightside) (sq_pt t I_zero)).
      * apply hconcat_right; rewrite sq_pt_t; lra.
      * transitivity (ah_map H2 (sq_pt (I_dbl' t) I_zero)).
        { apply comp_eval_SqSq.
          - rewrite Sq_rightside_t, !sq_pt_t, I_dbl'_eval; reflexivity.
          - rewrite Sq_rightside_s, !sq_pt_s; reflexivity. }
        { transitivity (q (I_dbl' t)); [ exact (ah_bot H2 (I_dbl' t)) | ].
          symmetry.
          apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ]. }
  - intro t.
    destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_leftside) (sq_pt t I_one)).
      * apply hconcat_left; rewrite sq_pt_t; exact Hle.
      * transitivity (ah_map H1 (sq_pt (I_dbl t) I_one)).
        { apply comp_eval_SqSq.
          - rewrite Sq_leftside_t, !sq_pt_t, I_dbl_eval; reflexivity.
          - rewrite Sq_leftside_s, !sq_pt_s; reflexivity. }
        { transitivity (p' (I_dbl t)); [ exact (ah_top H1 (I_dbl t)) | ].
          symmetry.
          apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ]. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_rightside) (sq_pt t I_one)).
      * apply hconcat_right; rewrite sq_pt_t; lra.
      * transitivity (ah_map H2 (sq_pt (I_dbl' t) I_one)).
        { apply comp_eval_SqSq.
          - rewrite Sq_rightside_t, !sq_pt_t, I_dbl'_eval; reflexivity.
          - rewrite Sq_rightside_s, !sq_pt_s; reflexivity. }
        { transitivity (q' (I_dbl' t)); [ exact (ah_top H2 (I_dbl' t)) | ].
          symmetry.
          apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ]. }
  - intro s.
    transitivity ((ah_map H1 ∘[Top] Sq_leftside) (sq_pt I_zero s)).
    + apply hconcat_left; rewrite sq_pt_t, ival_I_zero; lra.
    + transitivity (ah_map H1 (sq_pt I_zero s)); [ | exact (ah_left H1 s) ].
      apply comp_eval_SqSq.
      * rewrite Sq_leftside_t, !sq_pt_t, ival_I_zero; Rlin.
      * rewrite Sq_leftside_s, !sq_pt_s; reflexivity.
  - intro s.
    transitivity ((ah_map H2 ∘[Top] Sq_rightside) (sq_pt I_one s)).
    + apply hconcat_right; rewrite sq_pt_t, ival_I_one; lra.
    + transitivity (ah_map H2 (sq_pt I_one s)); [ | exact (ah_right H2 s) ].
      apply comp_eval_SqSq.
      * rewrite Sq_rightside_t, !sq_pt_t, ival_I_one; Rlin.
      * rewrite Sq_rightside_s, !sq_pt_s; reflexivity.
Defined.

End HomotopyConcat.

Definition path_concat_respects {X : TopSpace} {a b c : X}
           {p p' : Path X a b} {q q' : Path X b c}
           (E1 : PathHomotopy p p') (E2 : PathHomotopy q q') :
  PathHomotopy (path_concat p q) (path_concat p' q') :=
  hconcat E1 E2 (path_tgt p) (path_src q) (path_tgt p') (path_src q').

(** ** Reversal inverts, on both sides *)

Lemma path_rev_rev {X : TopSpace} {a b : X} (p : Path X a b) (x : Ipt) :
  path_map (path_rev (path_rev p)) x ≈ path_map p x.
Proof.
  transitivity (path_map p (I_rev (I_rev x))).
  - reflexivity.
  - apply Iap; rewrite !I_rev_eval; lra.
Qed.

Lemma concat_pointwise {X : TopSpace} (b : X) (p q p' q' : I_Top ~{Top}~> X)
      (Hp : p I_one ≈ b) (Hq : q I_zero ≈ b)
      (Hp' : p' I_one ≈ b) (Hq' : q' I_zero ≈ b)
      (Ep : ∀ x, p x ≈ p' x) (Eq : ∀ x, q x ≈ q' x) (x : Ipt) :
  concat_arrow b p q Hp Hq x ≈ concat_arrow b p' q' Hp' Hq' x.
Proof.
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - transitivity (p (I_dbl x)).
    + apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
    + transitivity (p' (I_dbl x)); [ exact (Ep (I_dbl x)) | ].
      symmetry; apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
  - apply Rnot_le_lt in Hnle.
    transitivity (q (I_dbl' x)).
    + apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
    + transitivity (q' (I_dbl' x)); [ exact (Eq (I_dbl' x)) | ].
      symmetry; apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
Qed.

(* The other inverse law comes from the first one applied to the reversed
   path, together with the pointwise identity p‾‾ = p; no second homotopy
   needs to be built. *)
Definition path_rev_inverse_left {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat (path_rev p) p) (const_path b).
Proof.
  unfold PathHomotopy.
  refine (ah_pointwise _ _ (inverse_homotopy (path_rev p))).
  - intro x.
    apply concat_pointwise.
    + intro y; reflexivity.
    + intro y; exact (path_rev_rev p y).
  - intro x; reflexivity.
Defined.

(** ** The fundamental groupoid *)

Definition PathHomotopy_Equivalence {X : TopSpace} (a b : X) :
  Equivalence (@PathHomotopy X a b).
Proof.
  constructor.
  - intro p; exact (ah_refl a b (path_map p) (path_src p) (path_tgt p)).
  - intros p q H; exact (ah_sym H).
  - intros p q r H1 H2; exact (ah_trans H1 H2).
Defined.

Definition Path_Setoid {X : TopSpace} (a b : X) : Setoid (Path X a b) := {|
  equiv        := @PathHomotopy X a b;
  setoid_equiv := PathHomotopy_Equivalence a b
|}.

#[local] Obligation Tactic := idtac.

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition FundamentalGroupoid (X : TopSpace) : Category := {|
  obj     := carrier (top_carrier X);
  hom     := fun a b => Path X a b;
  homset  := @Path_Setoid X;
  id      := @const_path X;
  compose := fun a b c q p => path_concat p q
|}.
Next Obligation.
  intros X x y z q q' E2 p p' E1.
  exact (path_concat_respects E1 E2).
Qed.
Next Obligation.
  intros X x y f; exact (unit_right_homotopy f).
Qed.
Next Obligation.
  intros X x y f; exact (unit_left_homotopy f).
Qed.
Next Obligation.
  intros X x y z w f g h; exact (assoc_homotopy h g f).
Qed.
Next Obligation.
  intros X x y z w f g h; exact (ah_sym (assoc_homotopy h g f)).
Qed.

(* Mac Lane §I.5: every arrow of the fundamental groupoid is invertible, the
   inverse of a class being the class of the reversed path. *)
Definition fundamental_groupoid_is_groupoid (X : TopSpace) :
  IsGroupoid (FundamentalGroupoid X).
Proof.
  intros a b f.
  refine (@Build_IsIsomorphism (FundamentalGroupoid X) a b f (path_rev f) _ _).
  - exact (path_rev_inverse_left f).
  - exact (inverse_homotopy f).
Defined.

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition equal_points_path {X : TopSpace} {a a' : X} (H : a ≈ a') :
  Path X a a' := {|
  path_map := const_arrow a;
  path_src := reflexivity a;
  path_tgt := H
|}.

Definition equal_points_iso {X : TopSpace} {a a' : X} (H : a ≈ a') :
  @Isomorphism (FundamentalGroupoid X) a a' :=
  giso (fundamental_groupoid_is_groupoid X) (equal_points_path H).

(** ** Path-connected spaces and the fundamental group *)

Definition PathConnected (X : TopSpace) : Type := ∀ a b : X, Path X a b.

Definition pathconnected_Connected {X : TopSpace} (K : PathConnected X) :
  Connected (FundamentalGroupoid X) :=
  @arrow_connected (FundamentalGroupoid X) K.

(* The fundamental group at a base point is the vertex group of the
   fundamental groupoid there (Structure/Groupoid.v's [vertex_group]). *)
Definition fundamental_group (X : TopSpace) (a : X) : GrpObject :=
  vertex_group (fundamental_groupoid_is_groupoid X) a.

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem fundamental_group_basepoint_independent {X : TopSpace}
        (K : PathConnected X) (a b : X) :
  MonIso (fundamental_group X a) (fundamental_group X b).
Proof.
  exact (connected_vertex_moniso (fundamental_groupoid_is_groupoid X)
           (pathconnected_Connected K) a b).
Defined.

(** ** Two paths that agree pointwise are homotopic *)

Definition pointwise_homotopic {X : TopSpace} {a b : X} (p q : Path X a b)
           (E : ∀ x : Ipt, path_map p x ≈ path_map q x) : PathHomotopy p q.
Proof.
  unfold PathHomotopy.
  refine (ah_pointwise _ _ (ah_refl a b (path_map p) (path_src p) (path_tgt p))).
  - intro x; reflexivity.
  - exact E.
Defined.

(** ** Every map from the interval to a two-point discrete space is constant *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition rclamp (r : R) : R := Rmax 0 (Rmin 1 r).

Lemma rclamp_lo (r : R) : 0 <= rclamp r.
Proof. unfold rclamp; apply Rmax_l. Qed.

Lemma rclamp_hi (r : R) : rclamp r <= 1.
Proof. unfold rclamp; apply Rmax_lub; [ lra | apply Rmin_l ]. Qed.

Lemma rclamp_id (r : R) : 0 <= r → r <= 1 → rclamp r = r.
Proof.
  intros H0 H1; unfold rclamp.
  rewrite Rmin_right by lra.
  apply Rmax_right; lra.
Qed.

Lemma rclamp_lip (r r' : R) : Rabs (rclamp r - rclamp r') <= Rabs (r - r').
Proof.
  unfold rclamp.
  apply Rle_trans with
    (r2 := Rmax (Rabs (0 - 0)) (Rabs (Rmin 1 r - Rmin 1 r'))).
  - apply Rabs_Rmax_le.
  - apply Rmax_lub.
    + assert (H : Rabs (0 - 0) = 0) by Rlin.
      rewrite H; apply Rabs_pos.
    + apply Rle_trans with (r2 := Rmax (Rabs (1 - 1)) (Rabs (r - r'))).
      * apply Rabs_Rmin_le.
      * apply Rmax_lub; [ | apply Rle_refl ].
        assert (H : Rabs (1 - 1) = 0) by Rlin.
        rewrite H; apply Rabs_pos.
Qed.

Definition clampI (r : R) : Ipt := mkI (rclamp r) (rclamp_lo r) (rclamp_hi r).

Section IntervalConnected.

Context (A : SetoidObject).
Context (dec : ∀ x y : A, (x ≈ y) + ((x ≈ y) → False)).
Context (f : I_Top ~{Top}~> Discrete_Top A).

Definition gval (r : R) : A := f (clampI r).

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma gval_locally_constant (r : R) :
  { d : R & ((0 < d) ∧ (∀ r' : R, Rabs (r - r') < d → gval r' ≈ gval r))%type }.
Proof.
  assert (HU : IsOpen (Discrete_Top A) (fun z : A => z ≈ f (clampI r))).
  { intros u v Huv Hu; rewrite <- Huv; exact Hu. }
  destruct (continuity f (fun z : A => z ≈ f (clampI r)) HU
              (clampI r) (reflexivity _)) as [d [Hd Hball]].
  exists d; split.
  - exact Hd.
  - intros r' Hr'.
    apply Hball.
    simpl.
    apply Rle_lt_trans with (r2 := Rabs (r - r')); [ | exact Hr' ].
    apply rclamp_lip.
Qed.

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition gsame (t : R) : Prop :=
  if dec (gval t) (gval 0) then True else False.

Lemma gsame_intro (t : R) : gval t ≈ gval 0 → gsame t.
Proof.
  intro H; unfold gsame.
  destruct (dec (gval t) (gval 0)) as [_ | Hno]; [ exact I | exact (Hno H) ].
Qed.

Lemma gsame_elim (t : R) : gsame t → gval t ≈ gval 0.
Proof.
  unfold gsame.
  destruct (dec (gval t) (gval 0)) as [Hyes | _];
    [ intros _; exact Hyes | contradiction ].
Qed.

Definition Egv (t : R) : Prop := 0 <= t /\ t <= 1 /\ gsame t.

Lemma gval_endpoints : gval 1 ≈ gval 0.
Proof.
  assert (Hb : bound Egv).
  { exact (@ex_intro R (is_upper_bound Egv) 1
             (fun t Ht => proj1 (proj2 Ht))). }
  assert (He : ex Egv).
  { exact (@ex_intro R Egv 0
             (conj (Rle_refl 0)
                (conj Rle_0_1 (gsame_intro 0 (reflexivity _))))). }
  destruct (completeness Egv Hb He) as [m [Hub Hlub]].
  assert (Hm0 : 0 <= m).
  { exact (Hub 0 (conj (Rle_refl 0)
                    (conj Rle_0_1 (gsame_intro 0 (reflexivity _))))). }
  assert (Hm1 : m <= 1).
  { exact (Hlub 1 (fun t Ht => proj1 (proj2 Ht))). }
  destruct (gval_locally_constant m) as [d [Hd Hball]].
  (* the value at the supremum already agrees, by approximation from below *)
  assert (Hgm : gval m ≈ gval 0).
  { destruct (dec (gval m) (gval 0)) as [Hyes | Hno]; [ exact Hyes | ].
    exfalso.
    assert (Hup : is_upper_bound Egv (m - d)).
    { intros t Ht.
      apply Rnot_lt_le.
      intro Hlt.
      apply Hno.
      transitivity (gval t).
      - symmetry.
        apply Hball.
        pose proof (Hub t Ht).
        Rlin.
      - exact (gsame_elim t (proj2 (proj2 Ht))). }
    pose proof (Hlub (m - d) Hup).
    lra. }
  (* and the supremum is the right endpoint *)
  assert (Hm : m = 1).
  { assert (Hnot : 1 <= m).
    { apply Rnot_lt_le.
      intro Hlt.
      pose proof (Hball (Rmin 1 (m + d/2))) as Hnear.
      assert (Hlo : 0 <= Rmin 1 (m + d/2)) by (apply Rmin_glb; lra).
      assert (Hhi : Rmin 1 (m + d/2) <= 1) by apply Rmin_l.
      assert (Hgt : m < Rmin 1 (m + d/2)) by (apply Rmin_glb_lt; lra).
      assert (Hclose : Rabs (m - Rmin 1 (m + d/2)) < d).
      { pose proof (Rmin_l 1 (m + d/2)).
        pose proof (Rmin_r 1 (m + d/2)).
        Rlin. }
      pose proof (Hub (Rmin 1 (m + d/2))
                    (conj Hlo (conj Hhi
                       (gsame_intro _
                          (transitivity (Hnear Hclose) Hgm))))).
      lra. }
    lra. }
  rewrite <- Hm; exact Hgm.
Qed.

Lemma f_endpoints : f I_one ≈ f I_zero.
Proof.
  assert (Hc1 : ival (clampI 1) = ival I_one).
  { change (rclamp 1 = ival I_one).
    rewrite rclamp_id by lra.
    symmetry; exact ival_I_one. }
  assert (Hc0 : ival (clampI 0) = ival I_zero).
  { change (rclamp 0 = ival I_zero).
    rewrite rclamp_id by lra.
    symmetry; exact ival_I_zero. }
  assert (H1 : f (clampI 1) ≈ f I_one) by exact (Iap f (clampI 1) I_one Hc1).
  assert (H0 : f (clampI 0) ≈ f I_zero) by exact (Iap f (clampI 0) I_zero Hc0).
  rewrite <- H1, <- H0.
  exact gval_endpoints.
Qed.

End IntervalConnected.

(* Rescaling by the target point turns the endpoint statement into constancy
   on the whole interval. *)
Lemma scale_lo (c : R) (H0 : 0 <= c) (H1 : c <= 1) (t : R) :
  0 <= t → t <= 1 → 0 <= c * t.
Proof. intros; nra. Qed.

Lemma scale_hi (c : R) (H0 : 0 <= c) (H1 : c <= 1) (t : R) :
  0 <= t → t <= 1 → c * t <= 1.
Proof. intros; nra. Qed.

Lemma scale_lip (c : R) (H0 : 0 <= c) (H1 : c <= 1) : RLip 2 (fun t => c * t).
Proof.
  intros x y.
  replace (c * x - c * y) with (c * (x - y)) by ring.
  rewrite Rabs_mult.
  apply Rmult_le_compat_r; [ apply Rabs_pos | Rlin ].
Qed.

Definition I_scale (c : R) (H0 : 0 <= c) (H1 : c <= 1) : I_Top ~{Top}~> I_Top :=
  I_arrow (fun t => c * t) 2 two_pos
    (scale_lo c H0 H1) (scale_hi c H0 H1) (scale_lip c H0 H1).

Theorem interval_to_discrete_constant_dec (A : SetoidObject)
        (dec : ∀ x y : A, (x ≈ y) + ((x ≈ y) → False))
        (f : I_Top ~{Top}~> Discrete_Top A) (x : Ipt) : f x ≈ f I_zero.
Proof.
  pose (s := I_scale (ival x) (ipt_lo x) (ipt_hi x)).
  pose proof (f_endpoints A dec (f ∘[Top] s)) as H.
  assert (E1 : ival (s I_one) = ival x).
  { change (ival x * ival I_one = ival x); rewrite ival_I_one; ring. }
  assert (E0 : ival (s I_zero) = ival I_zero).
  { change (ival x * ival I_zero = ival I_zero); rewrite ival_I_zero; ring. }
  assert (H1 : (f ∘[Top] s) I_one ≈ f x) by exact (comp_eval_I f s I_one x E1).
  assert (H0 : (f ∘[Top] s) I_zero ≈ f I_zero)
    by exact (comp_eval_I f s I_zero I_zero E0).
  rewrite <- H1, <- H0; exact H.
Qed.

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem interval_to_discrete_constant (f : I_Top ~{Top}~> Bool_Discrete)
        (x : Ipt) : f x = f I_zero.
Proof.
  exact (interval_to_discrete_constant_dec bool_setoid_object
           (fun a b => match Bool.bool_dec a b with
                       | left H => inl H
                       | right H => inr H
                       end) f x).
Qed.

(** ** The vertex-group inclusion is an equivalence *)

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fundamental_group_inclusion {X : TopSpace} (a : X) :
  Deloop (fundamental_group X a) ⟶ FundamentalGroupoid X :=
  vertex_incl (fundamental_groupoid_is_groupoid X) a.

Theorem fundamental_group_inclusion_equivalence {X : TopSpace}
        (K : PathConnected X) (a : X) :
  EquivalenceOfCategories (fundamental_group_inclusion a).
Proof.
  exact (connected_deloop_equiv (fundamental_groupoid_is_groupoid X)
           (pathconnected_Connected K) a).
Defined.

(** ** Non-vacuity: the construction separates two topologies on one set *)

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example bool_carriers_agree :
  top_carrier Bool_Discrete = top_carrier TwoPoint_Indiscrete := eq_refl.

(* On the discrete two-point space every path takes one and the same value
   at every parameter, by [interval_to_discrete_constant].  Hence there is no
   path from [true] to [false]. *)
Theorem no_path_true_false : Path Bool_Discrete true false → False.
Proof.
  intro p.
  assert (H : path_map p I_one = path_map p I_zero)
    by exact (interval_to_discrete_constant (path_map p) I_one).
  assert (Hs : path_map p I_zero = true) by exact (path_src p).
  assert (Ht : path_map p I_one = false) by exact (path_tgt p).
  rewrite H, Hs in Ht.
  discriminate.
Qed.

Theorem Bool_Discrete_not_pathconnected : PathConnected Bool_Discrete → False.
Proof. intro K; exact (no_path_true_false (K true false)). Qed.

(* And the fundamental groupoid itself is not connected, so the hypothesis of
   [fundamental_group_basepoint_independent] is a real restriction. *)
Theorem Bool_Discrete_pi_not_connected :
  Connected (FundamentalGroupoid Bool_Discrete) → False.
Proof.
  intro K.
  exact (no_path_true_false
           (connected_arrow (fundamental_groupoid_is_groupoid Bool_Discrete)
              K true false)).
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Bool_Discrete_loops_trivial (a : bool)
        (f : a ~{FundamentalGroupoid Bool_Discrete}~> a) : f ≈ id.
Proof.
  apply pointwise_homotopic.
  intro x.
  assert (H : path_map f x = path_map f I_zero)
    by exact (interval_to_discrete_constant (path_map f) x).
  assert (Hs : path_map f I_zero = a) by exact (path_src f).
  change (path_map f x = a).
  rewrite H; exact Hs.
Qed.

(* The indiscrete twin.  Every setoid map into it is continuous
   ([into_indiscrete_continuous] in Instance/Top.v), so the step function that
   jumps at the right endpoint is a path from a to b. *)
Definition two_pt_fun (a b : bool) (x : Ipt) : bool :=
  if Rle_dec 1 (ival x) then b else a.

Definition two_pt_setoid_map (a b : bool) :
  SetoidMorphism (top_carrier I_Top) bool_setoid_object.
Proof.
  refine {| morphism := two_pt_fun a b |}.
  intros x y Hxy.
  assert (H : ival x = ival y) by exact Hxy.
  unfold two_pt_fun; rewrite H; reflexivity.
Defined.

Definition two_pt_arrow (a b : bool) : I_Top ~{Top}~> TwoPoint_Indiscrete :=
  Build_ContinuousMorphism I_Top TwoPoint_Indiscrete (two_pt_setoid_map a b)
    (into_indiscrete_continuous I_Top bool_setoid_object
       (two_pt_setoid_map a b)).

Definition indiscrete_path (a b : bool) : Path TwoPoint_Indiscrete a b.
Proof.
  refine {| path_map := two_pt_arrow a b |}.
  - change (two_pt_fun a b I_zero = a).
    unfold two_pt_fun; rewrite ival_I_zero.
    destruct (Rle_dec 1 0) as [Hle | Hnle]; [ exfalso; lra | reflexivity ].
  - change (two_pt_fun a b I_one = b).
    unfold two_pt_fun; rewrite ival_I_one.
    destruct (Rle_dec 1 1) as [Hle | Hnle]; [ reflexivity | exfalso; apply Hnle; lra ].
Defined.

Definition TwoPoint_Indiscrete_pathconnected : PathConnected TwoPoint_Indiscrete :=
  indiscrete_path.

Definition TwoPoint_Indiscrete_pi_connected :
  Connected (FundamentalGroupoid TwoPoint_Indiscrete) :=
  pathconnected_Connected TwoPoint_Indiscrete_pathconnected.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TwoPoint_Indiscrete_basepoint_iso :
  MonIso (fundamental_group TwoPoint_Indiscrete true)
         (fundamental_group TwoPoint_Indiscrete false) :=
  fundamental_group_basepoint_independent TwoPoint_Indiscrete_pathconnected
    true false.

(* And the inclusion of the fundamental group at [true] into the whole
   fundamental groupoid is an equivalence of categories there. *)
Definition TwoPoint_Indiscrete_inclusion_equivalence :
  EquivalenceOfCategories (fundamental_group_inclusion (X:=TwoPoint_Indiscrete) true) :=
  fundamental_group_inclusion_equivalence TwoPoint_Indiscrete_pathconnected true.

(*
   本节说明 FundamentalGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition indiscrete_ah_fun {a b : bool} (p q : Path TwoPoint_Indiscrete a b)
           (z : BS_Sq) : bool :=
  if Rle_dec (sq_s z) (1/2) then path_map p (bs_fst z) else path_map q (bs_fst z).

Definition indiscrete_ah_setoid_map {a b : bool}
           (p q : Path TwoPoint_Indiscrete a b) :
  SetoidMorphism (top_carrier Sq_Top) bool_setoid_object.
Proof.
  refine {| morphism := indiscrete_ah_fun p q |}.
  intros z w Hzw.
  assert (H1 : sq_t z = sq_t w) by exact (fst Hzw).
  assert (H2 : sq_s z = sq_s w) by exact (snd Hzw).
  unfold indiscrete_ah_fun.
  rewrite H2.
  destruct (Rle_dec (sq_s w) (1/2)).
  - exact (Iap (path_map p) (bs_fst z) (bs_fst w) H1).
  - exact (Iap (path_map q) (bs_fst z) (bs_fst w) H1).
Defined.

Definition indiscrete_homotopy {a b : bool} (p q : Path TwoPoint_Indiscrete a b) :
  PathHomotopy p q.
Proof.
  unfold PathHomotopy.
  refine {| ah_map :=
              Build_ContinuousMorphism Sq_Top TwoPoint_Indiscrete
                (indiscrete_ah_setoid_map p q)
                (into_indiscrete_continuous Sq_Top bool_setoid_object
                   (indiscrete_ah_setoid_map p q)) |}.
  - intro t.
    change (indiscrete_ah_fun p q (sq_pt t I_zero) = path_map p t).
    unfold indiscrete_ah_fun; rewrite sq_pt_s, ival_I_zero.
    destruct (Rle_dec 0 (1/2)) as [Hle | Hnle];
      [ reflexivity | exfalso; apply Hnle; lra ].
  - intro t.
    change (indiscrete_ah_fun p q (sq_pt t I_one) = path_map q t).
    unfold indiscrete_ah_fun; rewrite sq_pt_s, ival_I_one.
    destruct (Rle_dec 1 (1/2)) as [Hle | Hnle];
      [ exfalso; lra | reflexivity ].
  - intro s.
    change (indiscrete_ah_fun p q (sq_pt I_zero s) = a).
    unfold indiscrete_ah_fun.
    destruct (Rle_dec (sq_s (sq_pt I_zero s)) (1/2)).
    + exact (path_src p).
    + exact (path_src q).
  - intro s.
    change (indiscrete_ah_fun p q (sq_pt I_one s) = b).
    unfold indiscrete_ah_fun.
    destruct (Rle_dec (sq_s (sq_pt I_one s)) (1/2)).
    + exact (path_tgt p).
    + exact (path_tgt q).
Defined.

Theorem TwoPoint_Indiscrete_loops_trivial (a : bool)
        (f : a ~{FundamentalGroupoid TwoPoint_Indiscrete}~> a) : f ≈ id.
Proof. exact (indiscrete_homotopy f (const_path (X:=TwoPoint_Indiscrete) a)). Qed.
