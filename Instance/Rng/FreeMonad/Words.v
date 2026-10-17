Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Monad.Morphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.FreeMonad.
Require Import Category.Instance.Ab.TensorPower.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * The tensor-algebra 单子 T, directly: T A ≅ ⨁ₙ A^{⊗n} （已译） *)

(*
 Book: Riehl, "Category Theory in Context", Example 5.5.7(ii), printed
 nLab: https://ncatlab.org/nlab/show/tensor+algebra

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Juxtaposition.

Context (A : AbObject).

Local Notation L := (carrier (cmon_setoid A)).

Fixpoint tw_mul (s t : TWTerm A) : TWTerm A :=
  match s with
  | tw_word w => tw_lmul w t
  | tw_zero => tw_zero
  | tw_plus s1 s2 => tw_plus (tw_mul s1 t) (tw_mul s2 t)
  | tw_neg s1 => tw_neg (tw_mul s1 t)
  end.

Lemma tw_mul_respects_l (s s' t : TWTerm A) :
  tw_eq A s s' → tw_eq A (tw_mul s t) (tw_mul s' t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t1 t1' _ IH1 _ IH2 | s s' _ IH
                 | s1 s2 s3 | s1 s2 | s1 | s1 | s1 s2 _ IH
                 | s1 s2 s3 _ IH1 _ IH2 ];
    simpl.
  - exact (tw_lmul_letter A u v a b Hab t).
  - exact (tw_lmul_lin A u v a b t).
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

Lemma tw_mul_respects_r (s t t' : TWTerm A) :
  tw_eq A t t' → tw_eq A (tw_mul s t) (tw_mul s t').
Proof.
  intro H.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - exact (tw_lmul_respects_r A w t t' H).
  - apply tw_refl.
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH1).
Qed.

Lemma tw_mul_lmul (w : list L) (t u : TWTerm A) :
  tw_mul (tw_lmul w t) u = tw_lmul w (tw_mul t u).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - apply tw_lmul_app.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma tw_mul_assoc (s t u : TWTerm A) :
  tw_mul (tw_mul s t) u = tw_mul s (tw_mul t u).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_mul_lmul.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma tw_mul_one_l (t : TWTerm A) : tw_mul (tw_word nil) t = t.
Proof. exact (tw_lmul_nil A t). Qed.

Lemma tw_mul_one_r (s : TWTerm A) : tw_mul s (tw_word nil) = s.
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - rewrite app_nil_r. reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma tw_mul_distr_l (s t u : TWTerm A) :
  tw_eq A (tw_mul s (tw_plus t u)) (tw_plus (tw_mul s t) (tw_mul s u)).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_refl.
  - exact (tw_zero_zero A).
  - refine (twe_trans (twe_plus IH1 IH2) _).
    exact (cmon_plus_interchange (TWAb A) _ _ _ _).
  - refine (twe_trans (twe_neg IH1) _). apply tw_neg_plus.
Qed.

Lemma tw_mul_zero_r (s : TWTerm A) : tw_eq A (tw_mul s tw_zero) tw_zero.
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_refl.
  - apply tw_refl.
  - exact (twe_trans (twe_plus IH1 IH2) (twe_zero_l tw_zero)).
  - exact (twe_trans (twe_neg IH1) (tw_neg_zero A)).
Qed.

(* 相关说明。 （已译） *)
Definition TWRing : RingObject := {|
  ring_rig := {|
    rig_setoid := cmon_setoid (TWAb A);
    rig_zero := tw_zero;
    rig_add := tw_plus;
    rig_one := tw_word nil;
    rig_mul := tw_mul;
    rig_add_respects := cmon_plus_respects (TWAb A);
    rig_mul_respects := fun s s' Hs t t' Ht =>
      twe_trans (tw_mul_respects_l s s' t Hs) (tw_mul_respects_r s' t t' Ht);
    rig_add_assoc := twe_assoc;
    rig_add_comm := twe_comm;
    rig_add_zero_l := twe_zero_l;
    rig_mul_assoc := fun s t u => tw_eq_of_eq (tw_mul_assoc s t u);
    rig_mul_one_l := fun t => tw_eq_of_eq (tw_mul_one_l t);
    rig_mul_one_r := fun s => tw_eq_of_eq (tw_mul_one_r s);
    rig_distr_l := tw_mul_distr_l;
    rig_distr_r := fun s t u => tw_refl _;
    rig_mul_zero_l := fun t => tw_refl _;
    rig_mul_zero_r := tw_mul_zero_r;
    rig_prop := cmon_prop (TWAb A)
  |};
  ring_neg := tw_neg;
  ring_neg_respects := ab_neg_respects (TWAb A);
  ring_neg_l := twe_neg_l
|}.

Example TWRing_ab : Rng_Forget_Ab TWRing = TWAb A := eq_refl.

Example tw_mul_words (u v : list L) :
  tw_mul (tw_word u) (tw_word v) = tw_word (u ++ v) := eq_refl.

End Juxtaposition.

Arguments tw_mul {A} _ _.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section WordExpr.

Context (A : AbObject).

Local Notation L := (carrier (cmon_setoid A)).

(* 相关说明。 （已译） *)
Fixpoint fr_word (w : list L) : FRTerm A :=
  match w with
  | nil => fr_one
  | a :: w' =>
      match w' with
      | nil => fr_gen a
      | _ :: _ => fr_mul (fr_gen a) (fr_word w')
      end
  end.

Lemma fr_word_cons (a : L) (w : list L) :
  fr_eq (fr_word (a :: w)) (fr_mul (fr_gen a) (fr_word w)).
Proof.
  destruct w as [ | b w ]; simpl.
  - exact (fre_sym (fre_mul_one_r (fr_gen a))).
  - apply fr_refl.
Qed.

Lemma fr_word_letter (u v : list L) (a b : L) (H : a ≈ b) :
  fr_eq (fr_word (u ++ a :: v)) (fr_word (u ++ b :: v)).
Proof.
  induction u as [ | c u IH ]; simpl.
  - destruct v; [ exact (fre_gen H) | exact (fre_mul (fre_gen H) (fr_refl _)) ].
  - destruct u; exact (fre_mul (fr_refl _) IH).
Qed.

Lemma fr_word_lin (u v : list L) (a b : L) :
  fr_eq (fr_word (u ++ cmon_plus A a b :: v))
        (fr_plus (fr_word (u ++ a :: v)) (fr_word (u ++ b :: v))).
Proof.
  induction u as [ | c u IH ]; simpl.
  - destruct v.
    + exact (fre_gen_plus a b).
    + refine (fre_trans (fre_mul (fre_gen_plus a b) (fr_refl _)) _).
      apply fre_distr_r.
  - destruct u;
      (refine (fre_trans (fre_mul (fr_refl _) IH) _); apply fre_distr_l).
Qed.

Lemma fr_word_app (w v : list L) :
  fr_eq (fr_word (w ++ v)) (fr_mul (fr_word w) (fr_word v)).
Proof.
  induction w as [ | a w IH ].
  - exact (fre_sym (fre_mul_one_l _)).
  - refine (fre_trans (fr_word_cons a (w ++ v)) _).
    refine (fre_trans (fre_mul (fr_refl _) IH) _).
    refine (fre_trans (fre_sym (fre_mul_assoc _ _ _)) _).
    exact (fre_mul (fre_sym (fr_word_cons a w)) (fr_refl _)).
Qed.

End WordExpr.

Arguments fr_word {A} _.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Iso.

Universes u p.

Context (A : Ab@{u p}).

Local Notation L := (carrier (cmon_setoid A)).

(* The one-letter word of 0 is 0. *)
Lemma tw_word_zero@{+} : tw_eq A (tw_word (cmon_zero A :: nil)) tw_zero.
Proof.
  set (x := tw_word (cmon_zero A :: nil)).
  assert (H : tw_eq A x (tw_plus x x)).
  { refine (twe_trans (twe_letter nil nil
                         (symmetry (cmon_plus_zero_l A (cmon_zero A)))) _).
    exact (twe_lin nil nil (cmon_zero A) (cmon_zero A)). }
  apply (ab_cancel_l (TWAb A) x).
  refine (twe_trans (twe_sym H) _).
  exact (twe_sym (cmon_plus_zero_r (TWAb A) x)).
Qed.

(* The insertion a ↦ ⟨a⟩ of A in degree one. *)
Definition tw_insert@{+} : A ~{Ab@{u p}}~> Rng_Forget_Ab (TWRing A).
Proof.
  unshelve refine (@Build_CMonHom A (Rng_Forget_Ab (TWRing A))
    (@Build_SetoidMorphism L (is_setoid (cmon_setoid A))
       (TWTerm A) (tw_Setoid A) (fun a => tw_word (a :: nil)) _) _ _).
  - intros a b H. exact (twe_letter nil nil H).
  - exact tw_word_zero.
  - intros a b. exact (twe_lin nil nil a b).
Defined.

(* to : T A → ⨁, SHARED extension 嵌入. （已译） *)
Definition tw_to_rng@{+} : FreeRngAbObject A ~{Rng@{u p}}~> TWRing A :=
  free_rng_ab_extend tw_insert.

(* 相关说明。 （已译） *)
Fixpoint tw_to_fr (t : TWTerm A) : FRTerm A :=
  match t with
  | tw_word w => fr_word w
  | tw_zero => fr_zero
  | tw_plus s t => fr_plus (tw_to_fr s) (tw_to_fr t)
  | tw_neg s => fr_neg (tw_to_fr s)
  end.

Lemma tw_to_fr_respects@{+} (s t : TWTerm A) :
  tw_eq A s t → fr_eq (tw_to_fr s) (tw_to_fr t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - exact (fr_word_letter A u v a b Hab).
  - exact (fr_word_lin A u v a b).
  - exact (fre_plus IH1 IH2).
  - exact (fre_neg IH).
  - apply fre_add_assoc.
  - apply fre_add_comm.
  - apply fre_add_zero_l.
  - apply fre_neg_l.
  - exact (fre_sym IH).
  - exact (fre_trans IH1 IH2).
Qed.

Definition tw_from@{+} : TWAb A ~{Ab@{u p}}~> Rng_Forget_Ab (FreeRngAb A).
Proof.
  unshelve refine (@Build_CMonHom (TWAb A) (Rng_Forget_Ab (FreeRngAb A))
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A) (FRTerm A) (fr_Setoid A)
       tw_to_fr _) _ _).
  - intros s t H. exact (tw_to_fr_respects s t H).
  - apply fr_refl.
  - intros s t. apply fr_refl.
Defined.

(* to ∘ 恒等 terms, LEIBNIZ. （已译） *)
Lemma fr_eval_word@{+} (w : list L) :
  fr_eval tw_insert (fr_word w) = tw_word w.
Proof.
  induction w as [ | a w IH ]; [ reflexivity | ].
  destruct w as [ | b w ]; [ reflexivity | ].
  change (tw_mul (tw_word (a :: nil)) (fr_eval tw_insert (fr_word (b :: w)))
            = tw_word (a :: b :: w)).
  rewrite IH. reflexivity.
Qed.

Lemma tw_to_from@{+} (t : TWTerm A) : rig_map tw_to_rng (tw_to_fr t) = t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
  - apply fr_eval_word.
  - reflexivity.
  - change (tw_plus (fr_eval tw_insert (tw_to_fr s))
                    (fr_eval tw_insert (tw_to_fr t)) = tw_plus s t).
    simpl in IHs, IHt. rewrite IHs, IHt. reflexivity.
  - change (tw_neg (fr_eval tw_insert (tw_to_fr s)) = tw_neg s).
    simpl in IHs. rewrite IHs. reflexivity.
Qed.

Lemma tw_to_fr_lmul@{+} (w : list L) (t : TWTerm A) :
  fr_eq (tw_to_fr (tw_lmul w t)) (fr_mul (fr_word w) (tw_to_fr t)).
Proof.
  induction t as [ v | | s IHs t IHt | s IHs ]; simpl.
  - apply fr_word_app.
  - exact (fre_sym (fr_mul_zero_r A _)).
  - refine (fre_trans (fre_plus IHs IHt) _).
    exact (fre_sym (fre_distr_l _ _ _)).
  - refine (fre_trans (fre_neg IHs) _).
    exact (fre_sym (rng_mul_neg_r (FreeRngAbObject A) _ _)).
Qed.

Lemma tw_to_fr_mul@{+} (s t : TWTerm A) :
  fr_eq (tw_to_fr (tw_mul s t)) (fr_mul (tw_to_fr s) (tw_to_fr t)).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_to_fr_lmul.
  - exact (fre_sym (fr_mul_zero_l A _)).
  - refine (fre_trans (fre_plus IH1 IH2) _).
    exact (fre_sym (fre_distr_r _ _ _)).
  - refine (fre_trans (fre_neg IH1) _).
    exact (fre_sym (rng_mul_neg_l (FreeRngAbObject A) _ _)).
Qed.

(* from ∘ 恒等 up ≈. （已译） *)
Lemma tw_from_to@{+} (t : FRTerm A) :
  fr_eq (tw_to_fr (rig_map tw_to_rng t)) t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - apply fr_refl.
  - apply fr_refl.
  - apply fr_refl.
  - exact (fre_plus IH1 IH2).
  - exact (fre_neg IH).
  - refine (fre_trans (tw_to_fr_mul _ _) _). exact (fre_mul IH1 IH2).
Qed.

(* Mac Lane's (a): T A ≅ ⨁ₙ A^{⊗n} in Ab. *)
Definition T_TW_iso@{+} : @Isomorphism Ab@{u p} (fobj[TF] A) (TWAb A).
Proof.
  unshelve refine
    (@Build_Isomorphism Ab@{u p} (fobj[TF] A) (TWAb A)
       (fmap[Rng_Forget_Ab] tw_to_rng) tw_from _ _).
  - intro t. exact (tw_eq_of_eq (tw_to_from t)).
  - intro t. exact (tw_from_to t).
Defined.

(* 相关说明。 （已译） *)
Example T_TW_ret@{+} (a : L) :
  cmon_map (to T_TW_iso) (cmon_map (@ret _ _ TM A) a) = tw_word (a :: nil)
  := eq_refl.

Example T_TW_to_fun@{+} (t : FRTerm A) :
  cmon_map (to T_TW_iso) t = fr_eval tw_insert t := eq_refl.

Example T_TW_from_word@{+} (w : list L) :
  cmon_map (from T_TW_iso) (tw_word w) = fr_word w := eq_refl.

Lemma T_TW_to_word@{+} (w : list L) :
  cmon_map (to T_TW_iso) (fr_word w) = tw_word w.
Proof. exact (fr_eval_word w). Qed.

(* from ∘ 恒等 nose at generator at product
 two generators. （已译） *)
Example T_TW_from_to_gen@{+} (a : L) :
  cmon_map (from T_TW_iso) (cmon_map (to T_TW_iso) (fr_gen a)) = fr_gen a
  := eq_refl.

Example T_TW_from_to_pair@{+} (a b : L) :
  cmon_map (from T_TW_iso)
    (cmon_map (to T_TW_iso) (fr_mul (fr_gen a) (fr_gen b)))
    = fr_mul (fr_gen a) (fr_gen b) := eq_refl.

End Iso.

Arguments tw_insert {A}.
Arguments tw_to_rng {A}.
Arguments tw_to_fr {A} _.
Arguments tw_from {A}.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Readings.

Universes u p.

Fixpoint tw_map {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B) (t : TWTerm A) :
  TWTerm B :=
  match t with
  | tw_word w => tw_word (List.map (cmon_map f) w)
  | tw_zero => tw_zero
  | tw_plus s t => tw_plus (tw_map f s) (tw_map f t)
  | tw_neg s => tw_neg (tw_map f s)
  end.

Lemma tw_map_lmul@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (w : list (carrier (cmon_setoid A))) (t : TWTerm A) :
  tw_map f (tw_lmul w t) = tw_lmul (List.map (cmon_map f) w) (tw_map f t).
Proof.
  induction t as [ v | | s IHs t IHt | s IHs ]; simpl.
  - rewrite map_app. reflexivity.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma tw_map_mul@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (s t : TWTerm A) :
  tw_map f (tw_mul s t) = tw_mul (tw_map f s) (tw_map f t).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_map_lmul.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma tw_to_relabel@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  rig_map (@tw_to_rng B) (fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t)
    = tw_map f (rig_map (@tw_to_rng A) t).
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl in IH1, IH2. rewrite IH1, IH2. reflexivity.
  - simpl in IH. rewrite IH. reflexivity.
  - simpl in IH1, IH2. rewrite IH1, IH2. symmetry. apply tw_map_mul.
Qed.

(* T f, read through the isomorphism, is f^{⊗n} on each word. *)
Theorem T_TW_map@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  tw_eq B (cmon_map (to (T_TW_iso B)) (cmon_map (fmap[TF] f) t))
          (tw_map f (cmon_map (to (T_TW_iso A)) t)).
Proof.
  refine (twe_trans (proper_morphism (cmon_map (to (T_TW_iso B))) _ _
                       (T_map_relabel f t)) _).
  exact (tw_eq_of_eq (tw_to_relabel f t)).
Qed.

(* 相关说明。 （已译） *)
Fixpoint tw_prod {A : Ab@{u p}} (ws : list (TWTerm A)) : TWTerm A :=
  match ws with
  | nil => tw_word nil
  | s :: ws' =>
      match ws' with
      | nil => s
      | _ :: _ => tw_mul s (tw_prod ws')
      end
  end.

(* μ on ⨁ₙ (⨁ₘ A^{⊗m})^{⊗n}: juxtapose the inner words. *)
Fixpoint tw_join {A : Ab@{u p}} (t : TWTerm (TWAb A)) : TWTerm A :=
  match t with
  | tw_word ws => tw_prod ws
  | tw_zero => tw_zero
  | tw_plus s t => tw_plus (tw_join s) (tw_join t)
  | tw_neg s => tw_neg (tw_join s)
  end.

Example tw_join_two@{+} {A : Ab@{u p}}
  (u v : list (carrier (cmon_setoid A))) :
  tw_join (@tw_word (TWAb A) (tw_word u :: tw_word v :: nil))
    = tw_word (u ++ v) := eq_refl.

Lemma tw_prod_cons@{+} {A : Ab@{u p}} (s : TWTerm A) (ws : list (TWTerm A)) :
  tw_prod (s :: ws) = tw_mul s (tw_prod ws).
Proof.
  destruct ws as [ | s' ws ]; simpl; [ | reflexivity ].
  symmetry. apply tw_mul_one_r.
Qed.

Lemma tw_prod_app@{+} {A : Ab@{u p}} (ws vs : list (TWTerm A)) :
  tw_prod (ws ++ vs) = tw_mul (tw_prod ws) (tw_prod vs).
Proof.
  induction ws as [ | s ws IH ].
  - simpl. symmetry. apply tw_mul_one_l.
  - simpl app. rewrite !tw_prod_cons, IH. symmetry. apply tw_mul_assoc.
Qed.

Lemma tw_join_lmul@{+} {A : Ab@{u p}} (ws : list (TWTerm A))
  (t : TWTerm (TWAb A)) :
  tw_eq A (tw_join (@tw_lmul (TWAb A) ws t)) (tw_mul (tw_prod ws) (tw_join t)).
Proof.
  induction t as [ vs | | s IHs t IHt | s IHs ]; simpl.
  - rewrite tw_prod_app. apply tw_refl.
  - exact (twe_sym (tw_mul_zero_r A _)).
  - refine (twe_trans (twe_plus IHs IHt) _).
    exact (twe_sym (tw_mul_distr_l A _ _ _)).
  - refine (twe_trans (twe_neg IHs) _).
    exact (twe_sym (rng_mul_neg_r (TWRing A) _ _)).
Qed.

Lemma tw_join_mul@{+} {A : Ab@{u p}} (s t : TWTerm (TWAb A)) :
  tw_eq A (tw_join (tw_mul s t)) (tw_mul (tw_join s) (tw_join t)).
Proof.
  induction s as [ ws | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_join_lmul.
  - apply tw_refl.
  - exact (twe_plus IH1 IH2).
  - refine (twe_trans (twe_neg IH1) _).
    exact (twe_sym (rng_mul_neg_l (TWRing A) _ _)).
Qed.

(* μ, read through the isomorphism, is juxtaposition. *)
Theorem T_TW_join@{+} {A : Ab@{u p}} (t : FRTerm (fobj[TF] A)) :
  tw_eq A (cmon_map (to (T_TW_iso A)) (cmon_map (@join _ _ TM A) t))
          (tw_join (tw_map (to (T_TW_iso A))
                      (cmon_map (to (T_TW_iso (fobj[TF] A))) t))).
Proof.
  induction t as [ s | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - apply tw_refl.
  - apply tw_refl.
  - apply tw_refl.
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - rewrite tw_map_mul.
    refine (twe_trans _ (twe_sym (tw_join_mul _ _))).
    exact (twe_trans (tw_mul_respects_l A _ _ _ IH1)
                     (tw_mul_respects_r A _ _ _ IH2)).
Qed.

(* 相关说明。 （已译） *)
Example T_TW_join_gen@{+} {A : Ab@{u p}} (s : FRTerm A) :
  cmon_map (to (T_TW_iso A))
    (cmon_map (@join _ _ TM A) (@fr_gen (fobj[TF] A) s))
  = tw_join (tw_map (to (T_TW_iso A))
       (cmon_map (to (T_TW_iso (fobj[TF] A))) (@fr_gen (fobj[TF] A) s)))
  := eq_refl.

Example T_TW_join_pair@{+} {A : Ab@{u p}} (s t : FRTerm A) :
  cmon_map (to (T_TW_iso A))
    (cmon_map (@join _ _ TM A)
       (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t)))
  = tw_join (tw_map (to (T_TW_iso A))
       (cmon_map (to (T_TW_iso (fobj[TF] A)))
          (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** ⨁ₙ (−)^{⊗n} 自函子 Ab, naturally isomorphic T （已译） *)

Lemma tw_map_respects@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (s t : TWTerm A) :
  tw_eq A s t → tw_eq B (tw_map f s) (tw_map f t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - rewrite !map_app. simpl.
    exact (twe_letter _ _ (proper_morphism (cmon_map f) _ _ Hab)).
  - rewrite !map_app. simpl.
    refine (twe_trans (twe_letter _ _ (cmon_map_plus f a b)) _).
    apply twe_lin.
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

Definition tw_map_hom@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B) :
  TWAb A ~{Ab@{u p}}~> TWAb B.
Proof.
  unshelve refine (@Build_CMonHom (TWAb A) (TWAb B)
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A) (TWTerm B) (tw_Setoid B)
       (tw_map f) _) _ _).
  - intros s t H. exact (tw_map_respects f s t H).
  - apply tw_refl.
  - intros s t. apply tw_refl.
Defined.

Lemma tw_word_pointwise@{+} {A B : Ab@{u p}} (f g : A ~{Ab@{u p}}~> B)
  (H : f ≈ g) (w : list (carrier (cmon_setoid A))) :
  tw_eq B (tw_word (map (cmon_map f) w)) (tw_word (map (cmon_map g) w)).
Proof.
  induction w as [ | a w IH ]; simpl.
  - apply tw_refl.
  - refine (twe_trans (twe_letter nil _ (H a)) _).
    exact (tw_lmul_respects_r B (cmon_map g a :: nil) _ _ IH).
Qed.

Lemma tw_map_id@{+} {A : Ab@{u p}} (t : TWTerm A) :
  tw_map (@id Ab@{u p} A) t = t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; cbn [tw_map].
  - f_equal. exact (map_id w).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma tw_map_comp@{+} {A B C : Ab@{u p}} (g : B ~{Ab@{u p}}~> C)
  (f : A ~{Ab@{u p}}~> B) (t : TWTerm A) :
  tw_map (g ∘[Ab@{u p}] f) t = tw_map g (tw_map f t).
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; cbn [tw_map].
  - f_equal. exact (eq_sym (map_map (cmon_map f) (cmon_map g) w)).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* ⨁ₙ (−)^{⊗n}: T f is f^{⊗n} on each word, computing. *)
Definition TWF@{+} : Ab@{u p} ⟶ Ab@{u p}.
Proof.
  unshelve refine (@Build_Functor Ab@{u p} Ab@{u p} TWAb
                     (fun A B f => tw_map_hom f) _ _ _).
  - intros A B f g H t. simpl.
    induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
    + exact (tw_word_pointwise f g H w).
    + apply tw_refl.
    + exact (twe_plus IHs IHt).
    + exact (twe_neg IHs).
  - intros A t. exact (tw_eq_of_eq (tw_map_id t)).
  - intros A B C g f t. exact (tw_eq_of_eq (tw_map_comp g f t)).
Defined.

Example TWF_obj@{+} (A : Ab@{u p}) : fobj[TWF] A = TWAb A := eq_refl.

Example TWF_map_word@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (w : list (carrier (cmon_setoid A))) :
  cmon_map (fmap[TWF] f) (tw_word w) = tw_word (map (cmon_map f) w)
  := eq_refl.

(* 相关说明。 （已译） *)
Definition T_TW_natural@{+} : TF ≈ TWF.
Proof.
  exists (fun A => T_TW_iso A).
  intros A B f t. simpl.
  refine (fre_trans (T_map_relabel f t) _).
  refine (fre_trans (fre_sym (tw_from_to B
            (fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t))) _).
  rewrite (tw_to_relabel f t).
  apply fr_refl.
Defined.

Example T_TW_natural_component@{+} (A : Ab@{u p}) :
  projT1 T_TW_natural A = T_TW_iso A := eq_refl.

End Readings.

Arguments tw_map {A B} f t.

(* ------------------------------------------------------------------------ *)
(* * ** ⨁ₙ (−)^{⊗n} 单子, directly, T ≅ it 单子 （已译） *)

Section DirectMonad.

Universes u p.

(* The word product respects ≈ in each factor... *)
Lemma tw_prod_letter@{+} {A : Ab@{u p}} (u v : list (TWTerm A))
  (s s' : TWTerm A) :
  tw_eq A s s' → tw_eq A (tw_prod (u ++ s :: v)) (tw_prod (u ++ s' :: v)).
Proof.
  intro H. induction u as [ | c u IH ]; simpl app.
  - rewrite !tw_prod_cons. exact (tw_mul_respects_l A _ _ _ H).
  - rewrite !tw_prod_cons. exact (tw_mul_respects_r A _ _ _ IH).
Qed.

(* ...and is additive in each. *)
Lemma tw_prod_lin@{+} {A : Ab@{u p}} (u v : list (TWTerm A))
  (s s' : TWTerm A) :
  tw_eq A (tw_prod (u ++ tw_plus s s' :: v))
          (tw_plus (tw_prod (u ++ s :: v)) (tw_prod (u ++ s' :: v))).
Proof.
  induction u as [ | c u IH ]; simpl app.
  - rewrite !tw_prod_cons. apply tw_refl.
  - rewrite !tw_prod_cons.
    refine (twe_trans (tw_mul_respects_r A _ _ _ IH) _).
    apply tw_mul_distr_l.
Qed.

(* So juxtaposition respects ≈, and μ is an arrow of Ab. *)
Lemma tw_join_respects@{+} {A : Ab@{u p}} (s t : TWTerm (TWAb A)) :
  tw_eq (TWAb A) s t → tw_eq A (tw_join s) (tw_join t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - exact (tw_prod_letter u v a b Hab).
  - exact (tw_prod_lin u v a b).
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

Definition tw_join_hom@{+} (A : Ab@{u p}) :
  TWAb (TWAb A) ~{Ab@{u p}}~> TWAb A.
Proof.
  unshelve refine (@Build_CMonHom (TWAb (TWAb A)) (TWAb A)
    (@Build_SetoidMorphism (TWTerm (TWAb A)) (tw_Setoid (TWAb A))
       (TWTerm A) (tw_Setoid A) tw_join _) _ _).
  - intros s t H. exact (tw_join_respects s t H).
  - apply tw_refl.
  - intros s t. apply tw_refl.
Defined.

(* 相关说明。 （已译） *)
Lemma tw_prod_letters@{+} {A : Ab@{u p}}
  (w : list (carrier (cmon_setoid A))) :
  tw_prod (map (fun a => @tw_word A (a :: nil)) w) = tw_word w.
Proof.
  induction w as [ | a w IH ]; [ reflexivity | ].
  cbn [map]. rewrite tw_prod_cons, IH. reflexivity.
Qed.

(* ...so μ ∘ T η = 1, LEIBNIZ. *)
Lemma tw_join_letters@{+} {A : Ab@{u p}} (t : TWTerm A) :
  tw_join (tw_map (@tw_insert A) t) = t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; cbn [tw_map tw_join].
  - exact (tw_prod_letters w).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma tw_prod_map@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (ws : list (TWTerm A)) :
  tw_prod (map (tw_map f) ws) = tw_map f (tw_prod ws).
Proof.
  induction ws as [ | s ws IH ]; [ reflexivity | ].
  simpl map. rewrite !tw_prod_cons, IH. symmetry. apply tw_map_mul.
Qed.

(* ...so μ is natural, LEIBNIZ. *)
Lemma tw_join_natural@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : TWTerm (TWAb A)) :
  tw_join (tw_map (tw_map_hom f) t) = tw_map f (tw_join t).
Proof.
  induction t as [ ws | | s IHs t IHt | s IHs ]; cbn [tw_map tw_join].
  - exact (tw_prod_map f ws).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma tw_join_prod@{+} {A : Ab@{u p}} (ws : list (TWTerm (TWAb A))) :
  tw_eq A (tw_join (tw_prod ws)) (tw_prod (map tw_join ws)).
Proof.
  induction ws as [ | s ws IH ]; [ apply tw_refl | ].
  simpl map. rewrite (@tw_prod_cons (TWAb A)), (@tw_prod_cons A).
  refine (twe_trans (tw_join_mul s (tw_prod ws)) _).
  exact (tw_mul_respects_r A _ _ _ IH).
Qed.

(* Mac Lane's direct description, "like text W": η the
 one-letter word, μ juxtaposition word words, laws
 proved induction terms without 伴随. （已译） *)
Definition TWMonad@{+} : @Monad Ab@{u p} TWF.
Proof.
  unshelve refine (@Build_Monad Ab@{u p} TWF (fun A => @tw_insert A)
                     (fun A => tw_join_hom A) _ _ _ _ _).
  - (* η natural, by conversion *)
    intros A B f a. apply tw_refl.
  - (* μ ∘ T μ ≈ μ ∘ μ T *)
    intros A t. simpl.
    induction t as [ ws | | s IHs t IHt | s IHs ]; simpl.
    + apply twe_sym. apply tw_join_prod.
    + apply tw_refl.
    + exact (twe_plus IHs IHt).
    + exact (twe_neg IHs).
  - (* μ ∘ T η ≈ 1 *)
    intros A t. exact (tw_eq_of_eq (tw_join_letters t)).
  - (* μ ∘ η T ≈ 1, by conversion *)
    intros A t. apply tw_refl.
  - (* μ natural *)
    intros A B f t. exact (tw_eq_of_eq (tw_join_natural f t)).
Defined.

(* η IS 嵌入 one-letter words, whole record; μ IS
 juxtaposition, word words product inner words; and
 μ ∘ η T = 1 nose. （已译） *)
Example TWMonad_ret@{+} (A : Ab@{u p}) :
  @ret _ _ TWMonad A = @tw_insert A := eq_refl.

Example TWMonad_join@{+} (A : Ab@{u p}) (t : TWTerm (TWAb A)) :
  cmon_map (@join _ _ TWMonad A) t = tw_join t := eq_refl.

Example TWMonad_join_word@{+} (A : Ab@{u p}) (ws : list (TWTerm A)) :
  cmon_map (@join _ _ TWMonad A) (@tw_word (TWAb A) ws) = tw_prod ws
  := eq_refl.

Example TWMonad_join_ret@{+} (A : Ab@{u p}) (t : TWTerm A) :
  cmon_map (@join _ _ TWMonad A)
    (cmon_map (@ret _ _ TWMonad (fobj[TWF] A)) t) = t := eq_refl.

(* The components [to (T_TW_iso A)] of (a), natural by [T_TW_map]... *)
Definition T_TW_transform@{+} : TF ⟹ TWF.
Proof.
  unshelve refine (@Build_Transform Ab@{u p} Ab@{u p} TF TWF
                     (fun A => to (T_TW_iso A)) _ _).
  - intros A B f t. simpl. apply twe_sym. exact (T_TW_map f t).
  - intros A B f t. simpl. exact (T_TW_map f t).
Defined.

(* ...form 态射 单子 T → TWMonad (Monad/Morphism.v's
 [MonadHom]): unit law conversion, multiplication law from
 [T_TW_join], [T_TW_map] [tw_join_respects]. （已译） *)
Definition T_TW_monad_hom@{+} : MonadHom TM TWMonad.
Proof.
  unshelve refine {| mh_transform := T_TW_transform |}.
  - intros A a. apply tw_refl.
  - intros A t. simpl.
    refine (twe_trans (T_TW_join t) _).
    apply tw_join_respects.
    apply twe_sym. exact (T_TW_map (to (T_TW_iso A)) t).
Defined.

Example T_TW_monad_hom_component@{+} (A : Ab@{u p}) :
  transform[mh_transform T_TW_monad_hom] A = to (T_TW_iso A) := eq_refl.

(* 相关说明。 （已译） *)
Lemma TW_T_natural@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : TWTerm A) :
  fr_eq (cmon_map (fmap[TF] f) (cmon_map (from (T_TW_iso A)) t))
        (cmon_map (from (T_TW_iso B)) (tw_map f t)).
Proof.
  refine (fre_trans (fre_sym (tw_from_to B _)) _).
  refine (fre_trans (tw_to_fr_respects B _ _ (T_TW_map f (tw_to_fr t))) _).
  exact (tw_to_fr_respects B _ _
           (tw_map_respects f _ _ (tw_eq_of_eq (tw_to_from A t)))).
Qed.

Definition TW_T_transform@{+} : TWF ⟹ TF.
Proof.
  unshelve refine (@Build_Transform Ab@{u p} Ab@{u p} TWF TF
                     (fun A => from (T_TW_iso A)) _ _).
  - intros A B f t. exact (TW_T_natural f t).
  - intros A B f t. exact (fre_sym (TW_T_natural f t)).
Defined.

(* ...and product word, sent T, μ word images, so
 they form 态射 单子 TWMonad → T. （已译） *)
Lemma tw_to_fr_prod@{+} {A : Ab@{u p}} (ws : list (TWTerm A)) :
  fr_eq (tw_to_fr (tw_prod ws))
        (fr_eval (@id Ab@{u p} (fobj[TF] A))
                 (@fr_word (fobj[TF] A) (map tw_to_fr ws))).
Proof.
  induction ws as [ | s ws IH ]; [ apply fr_refl | ].
  rewrite tw_prod_cons.
  refine (fre_trans (tw_to_fr_mul A _ _) _).
  refine (fre_trans (fre_mul (fr_refl _) IH) _).
  exact (fre_sym (fr_eval_respects (FreeRngAb A)
                    (@id Ab@{u p} (fobj[TF] A)) _ _
                    (fr_word_cons (fobj[TF] A) (tw_to_fr s)
                       (map tw_to_fr ws)))).
Qed.

Definition TW_T_monad_hom@{+} : MonadHom TWMonad TM.
Proof.
  unshelve refine {| mh_transform := TW_T_transform |}.
  - intros A a. apply fr_refl.
  - intros A t. simpl.
    induction t as [ ws | | s IHs t IHt | s IHs ]; simpl.
    + exact (tw_to_fr_prod ws).
    + apply fr_refl.
    + exact (fre_plus IHs IHt).
    + exact (fre_neg IHs).
Defined.

Example TW_T_monad_hom_component@{+} (A : Ab@{u p}) :
  transform[mh_transform TW_T_monad_hom] A = from (T_TW_iso A) := eq_refl.

(* T ≅ ⨁ₙ (−)^{⊗n} AS MONADS: two 态射 inverse in
 Monad/Morphism.v's 范畴 [Monads Ab] 单子 Ab. （已译） *)
Definition T_TW_monad_iso@{+} :
  @Isomorphism (Monads Ab@{u p}) (existT _ TF TM) (existT _ TWF TWMonad).
Proof.
  unshelve refine (@Build_Isomorphism (Monads Ab@{u p})
                     (existT _ TF TM) (existT _ TWF TWMonad)
                     T_TW_monad_hom TW_T_monad_hom _ _).
  - intros A t. simpl. exact (tw_eq_of_eq (tw_to_from A t)).
  - intros A t. simpl. exact (tw_from_to A t).
Defined.

Example T_TW_monad_iso_to@{+} : to T_TW_monad_iso = T_TW_monad_hom
  := eq_refl.

Example T_TW_monad_iso_from@{+} : from T_TW_monad_iso = TW_T_monad_hom
  := eq_refl.

End DirectMonad.
