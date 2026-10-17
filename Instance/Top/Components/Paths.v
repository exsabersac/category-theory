Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Coq.Reals.Cauchy.ConstructiveRcomplete.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Circle.
Require Import Category.Instance.Top.Components.

Generalizable All Variables.

(* * * Path components: π₀ colimit 函子 after P （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/connected+space
 Wikipedia: https://en.wikipedia.org/wiki/Locally_connected_space

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Definition ival_pred@{} (x : CReal) : Prop :=
  CRealLe (inject_Q 0) x /\ CRealLe x (inject_Q 1).

(* 相关说明。 （已译） *)
Program Definition IvalSetoid@{o} : SetoidObject@{o o} := {|
  carrier   := { x : CReal | ival_pred x };
  is_setoid := {| equiv := fun a b => CRealEq (proj1_sig a) (proj1_sig b) |}
|}.
Next Obligation.
  constructor.
  - intro x; exact (CRealEq_refl _).
  - intros x y H; exact (CRealEq_sym _ _ H).
  - intros x y z H1 H2; exact (CRealEq_trans _ _ _ H1 H2).
Qed.

Program Definition ival_incl@{o} :
  SetoidMorphism@{o o o} IvalSetoid@{o} RLine_setoid@{o} := {|
  morphism := fun a => proj1_sig a
|}.
Next Obligation. intros a b H; exact H. Qed.

(* 相关说明。 （已译） *)
Definition PInterval@{o} : PTop@{o} :=
  PSub PRLine@{o} IvalSetoid@{o} ival_incl@{o}.

Lemma ival_pred_0@{} : ival_pred (inject_Q 0).
Proof. split; [apply CRealLe_refl|apply inject_Q_le; discriminate]. Qed.

Lemma ival_pred_1@{} : ival_pred (inject_Q 1).
Proof. split; [apply inject_Q_le; discriminate|apply CRealLe_refl]. Qed.

Definition ival_zero@{o} : IvalSetoid@{o} :=
  exist _ (inject_Q 0) ival_pred_0.

Definition ival_one@{o} : IvalSetoid@{o} :=
  exist _ (inject_Q 1) ival_pred_1.

(* A point of a space, as a map out of the one-point space. *)
Definition ppoint_at@{o} (X : PTop@{o}) (x : X) : PMor@{o} PPoint@{o} X :=
  pdisc_mor unit_setoid_object@{o o} X (pconst unit_setoid_object@{o o} X x).

(* Riehl's endpoint inclusions 0, 1 : ∗ ⇉ I. *)
Definition ival_end0@{o} : PMor@{o} PPoint@{o} PInterval@{o} :=
  ppoint_at@{o} PInterval@{o} ival_zero@{o}.

Definition ival_end1@{o} : PMor@{o} PPoint@{o} PInterval@{o} :=
  ppoint_at@{o} PInterval@{o} ival_one@{o}.

(** ** Riehl's P : Top → Set^{•⇉•} *)

(* A hom-set of [PTopCat], as an object of [Sets]: Top(A, X). *)
Definition PHomSetoid@{o} (A X : PTop@{o}) : SetoidObject@{o o} :=
  {| carrier := PMor@{o} A X; is_setoid := PMor_Setoid@{o} A X |}.

Program Definition pprecomp@{o so | o < so +} {A B : PTop@{o}}
  (X : PTop@{o}) (k : PMor@{o} A B) :
  PHomSetoid@{o} B X ~{Sets@{o so}}~> PHomSetoid@{o} A X := {|
  morphism := fun q => pcompose q k
|}.
Next Obligation. intros A B X k q r H a; exact (H _). Qed.

Program Definition ppostcomp@{o so | o < so +} (A : PTop@{o})
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  PHomSetoid@{o} A X ~{Sets@{o so}}~> PHomSetoid@{o} A Y := {|
  morphism := fun q => pcompose h q
|}.
Next Obligation.
  intros A X Y h q r H a. simpl. exact (proper_morphism (pmap h) _ _ (H a)).
Qed.

(* 相关说明。 （已译） *)
Definition PPathPair_obj@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  Parallel@{p o} ⟶ Sets@{o so} :=
  APair (pprecomp@{o so} X ival_end0@{o}) (pprecomp@{o so} X ival_end1@{o}).

Example PPathPair_paths@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fobj[PPathPair_obj@{o so p} X] ParX = PHomSetoid@{o} PInterval@{o} X
  := eq_refl.

Example PPathPair_points@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fobj[PPathPair_obj@{o so p} X] ParY = PHomSetoid@{o} PPoint@{o} X
  := eq_refl.

Example PPathPair_ev0@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fmap[PPathPair_obj@{o so p} X]
    ((true; ParOne) : ParX ~{Parallel@{p o}}~> ParY)
    = pprecomp@{o so} X ival_end0@{o} := eq_refl.

Example PPathPair_ev1@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fmap[PPathPair_obj@{o so p} X]
    ((false; ParTwo) : ParX ~{Parallel@{p o}}~> ParY)
    = pprecomp@{o so} X ival_end1@{o} := eq_refl.

(* 相关说明。 （已译） *)
Program Definition PPathPair_map@{o so p | o < so, p <= o +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  PPathPair_obj@{o so p} X ⟹ PPathPair_obj@{o so p} Y := {|
  transform := fun j => match j with
    | ParX => ppostcomp@{o so} PInterval@{o} h
    | ParY => ppostcomp@{o so} PPoint@{o} h
    end
|}.
Next Obligation.
  intros X Y h [] [] [[] f] q; simpl;
    first [ reflexivity
          | exact (False_rect _ (ParHom_Y_X_absurd _ f))
          | exact (False_rect _ (ParHom_Id_false_absurd _ f)) ].
Qed.
Next Obligation.
  intros X Y h [] [] [[] f] q; simpl;
    first [ reflexivity
          | exact (False_rect _ (ParHom_Y_X_absurd _ f))
          | exact (False_rect _ (ParHom_Id_false_absurd _ f)) ].
Qed.

(* Riehl's Set^{•⇉•}, universes written out: 函子 at [so],
 transformations at [o], levels [Sets@{o so}] itself. （已译） *)
Definition ParSets@{o so p f | o < so, p <= o, o < f +} :
  Category@{so o o} :=
  @Fun@{p o so o so o f} Parallel@{p o} Sets@{o so}.

Program Definition PPathPair@{o so p f | o < so, p <= o, o < f +} :
  PTopCat@{o so} ⟶ ParSets@{o so p f} := {|
  fobj := PPathPair_obj@{o so p};
  fmap := fun X Y h => PPathPair_map@{o so p} h
|}.
Next Obligation.
  intros X Y f g H [] q; simpl; intro t; exact (H _).
Qed.
Next Obligation. intros X [] q t; reflexivity. Qed.
Next Obligation. intros X Y Z f g [] q t; reflexivity. Qed.

Example PPathPair_fmap_paths@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  transform[fmap[PPathPair@{o so p f}] h] ParX
    = ppostcomp@{o so} PInterval@{o} h := eq_refl.

(** ** π₀ := colim ∘ P *)

(* 相关说明。 （已译） *)
Definition PathColim@{o so p | o < so, p <= o +} :
  HasColimitsOfShape Parallel@{p o} Sets@{o so} :=
  Cocomplete_HasColimitsOfShape Sets_Cocomplete Parallel@{p o}.

(* Riehl's path components functor.  Its functoriality is the colimit
   functor's; nothing below proves a functor law. *)
Definition PPi0@{o so p f | o < so, p <= o, o < f +} :
  PTopCat@{o so} ⟶ Sets@{o so} :=
  ColimitFunctor PathColim@{o so p} ◯ PPathPair@{o so p f}.

Example PPi0_fobj@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o}) :
  fobj[PPi0@{o so p f}] X
    = colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) := eq_refl.

Example PPi0_fmap@{o so p f | o < so, p <= o, o < f +} {X Y : PTop@{o}}
  (h : PMor@{o} X Y) :
  fmap[PPi0@{o so p f}] h
    = Colim_map PathColim@{o so p} (PPathPair_map@{o so p} h) := eq_refl.

(* What colimit is, conversion: pairs (ParX; path) and
 (ParY; point), under 关系 diagram's arrows generate. （已译） *)
Example PPi0_carrier@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o}) :
  carrier (fobj[PPi0@{o so p f}] X)
    = { j : ParObj & carrier (fobj[PPathPair_obj@{o so p} X] j) }
  := eq_refl.

Example PPi0_equiv@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o})
  (c d : carrier (fobj[PPi0@{o so p f}] X)) :
  @equiv _ (fobj[PPi0@{o so p f}] X) c d
    = colim_rel (PPathPair_obj@{o so p} X) c d := eq_refl.

Example PPi0_inj_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  colim_inj PathColim@{o so p} (PPathPair_obj@{o so p} X) ParY x
    = existT _ ParY x := eq_refl.

(* 相关说明。 （已译） *)
Example PPi0_fmap_point@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParY x) = existT _ ParY (pcompose h x)
  := eq_refl.

Example PPi0_fmap_path@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (q : PMor@{o} PInterval@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParX q) = existT _ ParX (pcompose h q)
  := eq_refl.

(* 相关说明。 （已译） *)

Definition ppi0_to_coeq@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) ~{Sets@{o so}}~>
  SetsCoeq (pprecomp@{o so} X ival_end0@{o})
           (pprecomp@{o so} X ival_end1@{o}) :=
  colim_med PathColim@{o so p}
    (is_coequalizer_cocone _ _
       (sets_coeq_IsCoequalizer (pprecomp@{o so} X ival_end0@{o})
                                (pprecomp@{o so} X ival_end1@{o}))).

Program Definition ppi0_from_coeq@{o so p | o < so, p <= o +}
  (X : PTop@{o}) :
  SetsCoeq (pprecomp@{o so} X ival_end0@{o})
           (pprecomp@{o so} X ival_end1@{o})
    ~{Sets@{o so}}~>
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) := {|
  morphism := fun x => existT _ ParY x
|}.
Next Obligation.
  intros X x y H; simpl in *.
  induction H as [b1 b2 Hb | a | b1 b2 _ IH | b1 b2 b3 _ IH1 _ IH2].
  - exact (cr_point (PPathPair_obj X) ParY b1 b2 Hb).
  - exact (cr_trans _ _ _ _
             (cr_sym _ _ _
                (cr_glue (PPathPair_obj X) ParX ParY (true; ParOne) a))
             (cr_glue (PPathPair_obj X) ParX ParY (false; ParTwo) a)).
  - exact (cr_sym _ _ _ IH).
  - exact (cr_trans _ _ _ _ IH1 IH2).
Qed.

Program Definition PPi0_coeq_iso@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) :
  fobj[PPi0@{o so p f}] X ≅[Sets@{o so}]
  SetsCoeq (pprecomp@{o so} X ival_end0@{o})
           (pprecomp@{o so} X ival_end1@{o}) := {|
  to   := ppi0_to_coeq@{o so p} X;
  from := ppi0_from_coeq@{o so p} X
|}.
Next Obligation.
  intros X x; simpl. apply coeq_rel_refl.
Qed.
Next Obligation.
  intros X [[] x]; simpl.
  - exact (cr_sym _ _ _
             (cr_glue (PPathPair_obj X) ParX ParY (true; ParOne) x)).
  - apply colim_rel_refl.
Qed.

Example ppi0_to_coeq_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  ppi0_to_coeq@{o so p} X (existT _ ParY x) = x := eq_refl.

Example ppi0_to_coeq_path@{o so p | o < so, p <= o +} (X : PTop@{o})
  (q : PMor@{o} PInterval@{o} X) :
  ppi0_to_coeq@{o so p} X (existT _ ParX q) = pcompose q ival_end0@{o}
  := eq_refl.

Example ppi0_from_coeq_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  ppi0_from_coeq@{o so p} X x = existT _ ParY x := eq_refl.

(** ** Readback on the points of X *)

(* Evaluation of a path at a point of the interval. *)
Program Definition path_at@{o so | o < so +} (X : PTop@{o})
  (t : IvalSetoid@{o}) :
  PHomSetoid@{o} PInterval@{o} X ~{Sets@{o so}}~> pt_carrier X := {|
  morphism := fun q => pmap q t
|}.
Next Obligation. intros X t q r H; exact (H t). Qed.

Definition ppi0_to_points_fun@{o so p | o < so, p <= o +} (X : PTop@{o})
  (c : colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X)) : X :=
  match c with
  | existT _ ParX q => pmap q ival_zero@{o}
  | existT _ ParY x => pmap x ttt
  end.

(* 相关说明。 （已译） *)
Lemma ppi0_to_points_respects@{o so p | o < so, p <= o +} (X : PTop@{o})
  (c d : colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X)) :
  c ≈ d →
  coeq_rel (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
    (ppi0_to_points_fun@{o so p} X c) (ppi0_to_points_fun@{o so p} X d).
Proof.
  intro H; simpl in H.
  induction H as [[] x y Hxy | [] [] [[] f] x | c d _ IH | c d e _ IH1 _ IH2];
    simpl.
  - apply cq_base; exact (Hxy ival_zero@{o}).
  - apply cq_base; exact (Hxy ttt).
  - apply coeq_rel_refl.
  - exact (False_rect _ (ParHom_Id_false_absurd _ f)).
  - apply coeq_rel_refl.
  - exact (cq_glue (path_at@{o so} X ival_zero@{o})
             (path_at@{o so} X ival_one@{o}) x).
  - exact (False_rect _ (ParHom_Y_X_absurd _ f)).
  - exact (False_rect _ (ParHom_Y_X_absurd _ f)).
  - apply coeq_rel_refl.
  - exact (False_rect _ (ParHom_Id_false_absurd _ f)).
  - exact (cq_sym _ _ _ _ IH).
  - exact (cq_trans _ _ _ _ _ IH1 IH2).
Qed.

Program Definition ppi0_to_points@{o so p | o < so, p <= o +}
  (X : PTop@{o}) :
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) ~{Sets@{o so}}~>
  SetsCoeq (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
  := {|
  morphism := ppi0_to_points_fun@{o so p} X
|}.
Next Obligation.
  intros X c d H. exact (ppi0_to_points_respects@{o so p} X c d H).
Qed.

Program Definition ppi0_from_points@{o so p | o < so, p <= o +}
  (X : PTop@{o}) :
  SetsCoeq (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
    ~{Sets@{o so}}~>
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) := {|
  morphism := fun x => existT _ ParY (ppoint_at@{o} X x)
|}.
Next Obligation.
  intros X x y H; simpl in *.
  induction H as [a b Hab | q | a b _ IH | a b c _ IH1 _ IH2].
  - apply (cr_point (PPathPair_obj X) ParY). intro u; exact Hab.
  - refine (cr_trans (PPathPair_obj X) _
              (existT _ ParY (pcompose q ival_end0@{o})) _ _ _).
    + apply (cr_point (PPathPair_obj X) ParY). intro u; reflexivity.
    + refine (cr_trans (PPathPair_obj X) _ (existT _ ParX q) _ _ _).
      * exact (cr_sym _ _ _ (cr_glue (PPathPair_obj X) ParX ParY
                                     (true; ParOne) q)).
      * refine (cr_trans (PPathPair_obj X) _
                  (existT _ ParY (pcompose q ival_end1@{o})) _ _ _).
        -- exact (cr_glue (PPathPair_obj X) ParX ParY (false; ParTwo) q).
        -- apply (cr_point (PPathPair_obj X) ParY). intro u; reflexivity.
  - exact (cr_sym _ _ _ IH).
  - exact (cr_trans _ _ _ _ IH1 IH2).
Qed.

(* Riehl's "quotient set points X 关系 that
 identifies any pair points connected path", 关系
 being 等价 关系 paths generate. （已译） *)
Program Definition PPi0_points_iso@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) :
  fobj[PPi0@{o so p f}] X ≅[Sets@{o so}]
  SetsCoeq (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
  := {|
  to   := ppi0_to_points@{o so p} X;
  from := ppi0_from_points@{o so p} X
|}.
Next Obligation.
  intros X x; simpl. apply coeq_rel_refl.
Qed.
Next Obligation.
  intros X [[] x]; simpl.
  - refine (cr_trans (PPathPair_obj X) _
              (existT _ ParY (pcompose x ival_end0@{o})) _ _ _).
    + apply (cr_point (PPathPair_obj X) ParY). intro u; reflexivity.
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj X) ParX ParY
                                   (true; ParOne) x)).
  - apply (cr_point (PPathPair_obj X) ParY). intros []; reflexivity.
Qed.

Example ppi0_to_points_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  ppi0_to_points@{o so p} X (existT _ ParY x) = pmap x ttt := eq_refl.

Example ppi0_from_points_at@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : X) :
  ppi0_from_points@{o so p} X x = existT _ ParY (ppoint_at@{o} X x)
  := eq_refl.

(* * ** The interval connected, maps 进入 two-point space （已译） *)

Section Bisection.

Local Open Scope Q_scope.

(* Rational points of the interval, clamped into [0,1]. *)
Definition ibis_clamp@{} (q : Q) : Q := Qmax 0 (Qmin 1 q).

Lemma ibis_clamp_lo@{} (q : Q) : 0 <= ibis_clamp q.
Proof. apply Q.le_max_l. Qed.

Lemma ibis_clamp_hi@{} (q : Q) : ibis_clamp q <= 1.
Proof. apply Q.max_lub; [discriminate|apply Q.le_min_l]. Qed.

Lemma ibis_clamp_id@{} (q : Q) : 0 <= q → q <= 1 → ibis_clamp q == q.
Proof.
  intros H0 H1. unfold ibis_clamp.
  rewrite (Q.min_r 1 q H1). apply Q.max_r. exact H0.
Qed.

Lemma ibis_clamp_ival@{} (q : Q) : ival_pred (inject_Q (ibis_clamp q)).
Proof.
  split; apply inject_Q_le; [apply ibis_clamp_lo|apply ibis_clamp_hi].
Qed.

Definition ibis_pt@{o} (q : Q) : IvalSetoid@{o} :=
  exist _ (inject_Q (ibis_clamp q)) (ibis_clamp_ival q).

(* The value of a map into [PBool] at a rational point. *)
Definition ibis_val@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) (q : Q) :
  bool := pmap γ (ibis_pt@{o} q).

Lemma ibis_val_proper@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (q r : Q) : q == r → ibis_val@{o} γ q = ibis_val@{o} γ r.
Proof.
  intro H. unfold ibis_val.
  apply (proper_morphism (pmap γ)). simpl.
  apply inject_Q_morph_T. unfold ibis_clamp. rewrite H. reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition ibis_step@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (ab : Q * Q) : Q * Q :=
  let m := (fst ab + snd ab) * (1 # 2) in
  if ibis_val@{o} γ m then (fst ab, m) else (m, snd ab).

Fixpoint ibis_stage@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) (n : nat) :
  Q * Q :=
  match n with
  | O => (0, 1)
  | S n => ibis_step@{o} γ (ibis_stage γ n)
  end.

Fixpoint ibis_width@{} (n : nat) : Q :=
  match n with O => 1 | S n => ibis_width n * (1 # 2) end.

Lemma ibis_width_pos@{} (n : nat) : 0 < ibis_width n.
Proof. induction n; simpl; [reflexivity|]. lra. Qed.

Lemma ibis_width_bound@{} (n : nat) :
  ibis_width n <= 1 # Pos.of_succ_nat n.
Proof.
  induction n; simpl; [apply Qle_refl|].
  apply (Qle_trans _ ((1 # Pos.of_succ_nat n) * (1 # 2))).
  - apply Qmult_le_compat_r; [exact IHn|discriminate].
  - unfold Qle, Qmult. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul.
    pose proof (Zpos_P_of_succ_nat n).
    pose proof (Zpos_P_of_succ_nat (S n)).
    lia.
Qed.

Lemma ibis_width_mono@{} (n k : nat) : ibis_width (k + n) <= ibis_width n.
Proof.
  induction k; simpl; [apply Qle_refl|].
  pose proof (ibis_width_pos (k + n)). lra.
Qed.

Lemma ibis_inv@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (n : nat) :
  ibis_val@{o} γ (fst (ibis_stage@{o} γ n)) = false /\
  ibis_val@{o} γ (snd (ibis_stage@{o} γ n)) = true /\
  snd (ibis_stage@{o} γ n) - fst (ibis_stage@{o} γ n) == ibis_width n /\
  0 <= fst (ibis_stage@{o} γ n) /\ snd (ibis_stage@{o} γ n) <= 1.
Proof.
  induction n as [|n [Ha [Hb [Hw [H0 H1]]]]]; simpl.
  - split; [exact g0|].
    split; [exact g1|split; [reflexivity|split; discriminate]].
  - unfold ibis_step. destruct (ibis_stage γ n) as [a b]; simpl in *.
    pose proof (ibis_width_pos n).
    destruct (ibis_val γ ((a + b) * (1 # 2))) eqn:Hm; simpl.
    + split; [exact Ha|split; [exact Hm|split; [lra|split; lra]]].
    + split; [exact Hm|split; [exact Hb|split; [lra|split; lra]]].
Qed.

Lemma ibis_nest@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true)
  (n k : nat) :
  fst (ibis_stage@{o} γ n) <= fst (ibis_stage@{o} γ (k + n)) /\
  snd (ibis_stage@{o} γ (k + n)) <= snd (ibis_stage@{o} γ n).
Proof.
  induction k as [|k [IHa IHb]]; simpl; [split; apply Qle_refl|].
  pose proof (ibis_inv γ g0 g1 (k + n)) as [_ [_ [Hw _]]].
  pose proof (ibis_width_pos (k + n)).
  unfold ibis_step. destruct (ibis_stage γ (k + n)) as [a b]; simpl in *.
  destruct (ibis_val γ ((a + b) * (1 # 2))); simpl; split; lra.
Qed.

Lemma ibis_left_close@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true)
  (n i j : nat) : (n <= i)%nat → (n <= j)%nat →
  Qabs (fst (ibis_stage@{o} γ i) - fst (ibis_stage@{o} γ j))
    <= ibis_width n.
Proof.
  intros Hi Hj.
  destruct (Nat.le_exists_sub n i Hi) as [ki [-> _]].
  destruct (Nat.le_exists_sub n j Hj) as [kj [-> _]].
  pose proof (ibis_nest γ g0 g1 n ki) as [Ai Bi].
  pose proof (ibis_nest γ g0 g1 n kj) as [Aj Bj].
  pose proof (ibis_inv γ g0 g1 n) as [_ [_ [Hw _]]].
  pose proof (ibis_inv γ g0 g1 (ki + n)) as [_ [_ [Hwi _]]].
  pose proof (ibis_inv γ g0 g1 (kj + n)) as [_ [_ [Hwj _]]].
  pose proof (ibis_width_pos (ki + n)).
  pose proof (ibis_width_pos (kj + n)).
  apply Qabs_case; intros; lra.
Qed.

Lemma ibis_width_small@{} (p : positive) (n : nat) :
  (Pos.to_nat p <= n)%nat → ibis_width n <= 1 # p.
Proof.
  intro H.
  destruct (Nat.le_exists_sub _ _ H) as [k [-> _]].
  apply (Qle_trans _ (ibis_width (Pos.to_nat p))); [apply ibis_width_mono|].
  apply (Qle_trans _ _ _ (ibis_width_bound _)).
  unfold Qle; simpl. rewrite Zpos_P_of_succ_nat, positive_nat_Z. lia.
Qed.

(* 相关说明。 （已译） *)
Definition ibis_seq@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) (i : nat) :
  CReal := inject_Q (fst (ibis_stage@{o} γ i)).

Lemma ibis_seq_cauchy@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  Un_cauchy_mod (ibis_seq@{o} γ).
Proof.
  intro p. exists (Pos.to_nat p). intros i j Hi Hj.
  unfold ibis_seq. rewrite inject_Q_minus, <- Qabs_Rabs.
  apply inject_Q_le.
  apply (Qle_trans _ _ _ (ibis_left_close γ g0 g1 (Pos.to_nat p) i j Hi Hj)).
  apply ibis_width_small, le_n.
Qed.

Definition ibis_lim@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) : CReal :=
  projT1 (Rcauchy_complete (ibis_seq@{o} γ) (ibis_seq_cauchy@{o} γ g0 g1)).

Definition ibis_lim_cv@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  seq_cv (ibis_seq@{o} γ) (ibis_lim@{o} γ g0 g1) :=
  projT2 (Rcauchy_complete (ibis_seq@{o} γ) (ibis_seq_cauchy@{o} γ g0 g1)).

Lemma ibis_q_pos_inv@{} (d : Q) : 0 < d → { p : positive & 1 # p <= d }.
Proof.
  destruct d as [n m]. intro H. exists m.
  unfold Qlt in H; simpl in H. unfold Qle; simpl. nia.
Qed.

Lemma ibis_cv_ge@{o +} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (c : Q) :
  (∀ i, c <= fst (ibis_stage@{o} γ i)) →
  CRealLe (inject_Q c) (ibis_lim@{o} γ g0 g1).
Proof.
  intros Hc Hlt.
  destruct (CRealQ_dense _ _ Hlt) as [q [Hlq Hqc]].
  pose proof (lt_inject_Q _ _ Hqc) as Hq.
  destruct (ibis_q_pos_inv (c - q)) as [p Hp]; [lra|].
  destruct (ibis_lim_cv γ g0 g1 p) as [N HN].
  specialize (HN N (le_n N)).
  assert (H1 : CRealLt (ibis_seq γ N) (inject_Q c)).
  { apply (CReal_le_lt_trans _
             (CReal_plus (ibis_lim γ g0 g1) (inject_Q (1 # p)))).
    - apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
               (CReal_abs (CReal_minus (ibis_seq γ N) (ibis_lim γ g0 g1))))).
      + apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
                 (CReal_minus (ibis_seq γ N) (ibis_lim γ g0 g1)))).
        * unfold CReal_minus. rewrite CReal_plus_comm, CReal_plus_assoc,
            CReal_plus_opp_l, CReal_plus_0_r. apply CRealLe_refl.
        * apply CReal_plus_le_compat_l, CReal_le_abs.
      + apply CReal_plus_le_compat_l. exact HN.
    - apply (CReal_lt_le_trans _
               (CReal_plus (inject_Q q) (inject_Q (1 # p)))).
      + rewrite !(CReal_plus_comm _ (inject_Q (1 # p))).
        apply CReal_plus_lt_compat_l. exact Hlq.
      + rewrite <- inject_Q_plus. apply inject_Q_le. lra. }
  pose proof (lt_inject_Q _ _ H1). pose proof (Hc N). lra.
Qed.

Lemma ibis_cv_le@{o +} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (c : Q) :
  (∀ i, fst (ibis_stage@{o} γ i) <= c) →
  CRealLe (ibis_lim@{o} γ g0 g1) (inject_Q c).
Proof.
  intros Hc Hlt.
  destruct (CRealQ_dense _ _ Hlt) as [q [Hcq Hql]].
  pose proof (lt_inject_Q _ _ Hcq) as Hq.
  destruct (ibis_q_pos_inv (q - c)) as [p Hp]; [lra|].
  destruct (ibis_lim_cv γ g0 g1 p) as [N HN].
  specialize (HN N (le_n N)).
  assert (H1 : CRealLt (inject_Q c) (ibis_seq γ N)).
  { apply (CReal_le_lt_trans _
             (CReal_plus (inject_Q q) (inject_Q (- (1 # p))))).
    - rewrite <- inject_Q_plus. apply inject_Q_le. lra.
    - apply (CReal_lt_le_trans _
               (CReal_plus (ibis_lim γ g0 g1) (inject_Q (- (1 # p))))).
      + rewrite !(CReal_plus_comm _ (inject_Q (- (1 # p)))).
        apply CReal_plus_lt_compat_l. exact Hql.
      + rewrite CReal_abs_minus_sym in HN.
        apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
                 (CReal_opp (CReal_abs
                    (CReal_minus (ibis_lim γ g0 g1) (ibis_seq γ N)))))).
        * apply CReal_plus_le_compat_l.
          rewrite opp_inject_Q. apply CReal_opp_ge_le_contravar. exact HN.
        * apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
                   (CReal_opp (CReal_minus (ibis_lim γ g0 g1)
                                           (ibis_seq γ N))))).
          -- apply CReal_plus_le_compat_l. apply CReal_opp_ge_le_contravar.
             apply CReal_le_abs.
          -- unfold CReal_minus.
             rewrite CReal_opp_plus_distr, CReal_opp_involutive.
             rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
             apply CRealLe_refl. }
  pose proof (lt_inject_Q _ _ H1). pose proof (Hc N). lra.
Qed.

Lemma ibis_lim_ival@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  ival_pred (ibis_lim@{o} γ g0 g1).
Proof.
  split.
  - apply ibis_cv_ge. intro i.
    exact (proj1 (proj2 (proj2 (proj2 (ibis_inv γ g0 g1 i))))).
  - apply ibis_cv_le. intro i.
    pose proof (ibis_inv γ g0 g1 i) as [_ [_ [Hw [H0 H1]]]].
    pose proof (ibis_width_pos i). lra.
Qed.

Definition ibis_lim_pt@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  IvalSetoid@{o} :=
  exist _ (ibis_lim@{o} γ g0 g1) (ibis_lim_ival@{o} γ g0 g1).

Lemma ibis_seq_in@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (N : nat) :
  CRealEq (inject_Q (ibis_clamp (fst (ibis_stage@{o} γ N))))
          (ibis_seq@{o} γ N).
Proof.
  apply inject_Q_morph_T.
  pose proof (ibis_inv γ g0 g1 N) as [_ [_ [Hw [H0 H1]]]].
  pose proof (ibis_width_pos N). apply ibis_clamp_id; lra.
Qed.

Lemma ibis_right_in@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (N : nat) :
  CRealEq (inject_Q (ibis_clamp (snd (ibis_stage@{o} γ N))))
          (inject_Q (snd (ibis_stage@{o} γ N))).
Proof.
  apply inject_Q_morph_T.
  pose proof (ibis_inv γ g0 g1 N) as [_ [_ [Hw [H0 H1]]]].
  pose proof (ibis_width_pos N). apply ibis_clamp_id; lra.
Qed.

(* The map 常值 ball about limit, both left ends
 (valued [false]) right ends (valued [true]) enter every such
 ball. （已译） *)
Theorem ibis_contra@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) : False.
Proof.
  destruct (pmap γ (ibis_lim_pt γ g0 g1)) eqn:Hl.
  - assert (Ho : POpen PBool (fun b => b = true)).
    { intros x y Hxy Hx. simpl in Hxy. congruence. }
    destruct (pcont γ _ Ho) as [U [HU HUs]].
    pose proof (proj1 (HUs (ibis_lim_pt γ g0 g1)) Hl) as Ul.
    destruct (HU (ibis_lim γ g0 g1) Ul) as [e [He Hball]].
    destruct (ibis_q_pos_inv e He) as [p Hp].
    destruct (ibis_lim_cv γ g0 g1 p) as [N HN].
    specialize (HN N (le_n N)).
    assert (Hb : rball (ibis_lim γ g0 g1)
                   (inject_Q (ibis_clamp (fst (ibis_stage γ N)))) e).
    { unfold rball. rewrite (ibis_seq_in γ g0 g1 N).
      apply (CReal_le_trans _ _ _ HN). apply inject_Q_le. exact Hp. }
    pose proof (proj2 (HUs (ibis_pt (fst (ibis_stage γ N))))
                  (Hball _ Hb)) as Hg.
    pose proof (proj1 (ibis_inv γ g0 g1 N)) as Hf. unfold ibis_val in *.
    rewrite Hf in Hg. discriminate Hg.
  - assert (Ho : POpen PBool (fun b => b = false)).
    { intros x y Hxy Hx. simpl in Hxy. congruence. }
    destruct (pcont γ _ Ho) as [U [HU HUs]].
    pose proof (proj1 (HUs (ibis_lim_pt γ g0 g1)) Hl) as Ul.
    destruct (HU (ibis_lim γ g0 g1) Ul) as [e [He Hball]].
    destruct (ibis_q_pos_inv (e * (1 # 2))) as [p Hp]; [lra|].
    destruct (ibis_lim_cv γ g0 g1 p) as [N0 HN].
    pose (N := Nat.max N0 (Pos.to_nat p)).
    specialize (HN N (Nat.le_max_l _ _)).
    pose proof (ibis_width_small p N (Nat.le_max_r _ _)) as HW.
    pose proof (ibis_inv γ g0 g1 N) as [_ [Ht [Hw [H0 H1]]]].
    assert (Hb : rball (ibis_lim γ g0 g1)
                   (inject_Q (ibis_clamp (snd (ibis_stage γ N)))) e).
    { unfold rball. rewrite (ibis_right_in γ g0 g1 N).
      assert (E : CRealEq
                (CReal_minus (inject_Q (snd (ibis_stage γ N)))
                             (ibis_lim γ g0 g1))
                (CReal_plus
                   (CReal_minus (inject_Q (snd (ibis_stage γ N)))
                                (ibis_seq γ N))
                   (CReal_minus (ibis_seq γ N) (ibis_lim γ g0 g1)))).
      { unfold CReal_minus. ring. }
      rewrite E.
      apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
      apply (CReal_le_trans _
               (CReal_plus (inject_Q (1 # p)) (inject_Q (1 # p)))).
      - apply CReal_plus_le_compat; [|exact HN].
        unfold ibis_seq. rewrite inject_Q_minus, <- Qabs_Rabs.
        apply inject_Q_le.
        pose proof (ibis_width_pos N).
        apply Qabs_case; intros; lra.
      - rewrite <- inject_Q_plus. apply inject_Q_le. lra. }
    pose proof (proj2 (HUs (ibis_pt (snd (ibis_stage γ N))))
                  (Hball _ Hb)) as Hg.
    unfold ibis_val in *. rewrite Ht in Hg. discriminate Hg.
Qed.

End Bisection.

(* 相关说明。 （已译） *)
Theorem interval_bool_endpoints@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) :
  pmap γ ival_zero@{o} = pmap γ ival_one@{o}.
Proof.
  assert (E0 : pmap γ ival_zero = ibis_val γ 0).
  { apply (proper_morphism (pmap γ)). simpl.
    apply inject_Q_morph_T. reflexivity. }
  assert (E1 : pmap γ ival_one = ibis_val γ 1).
  { apply (proper_morphism (pmap γ)). simpl.
    apply inject_Q_morph_T. reflexivity. }
  rewrite E0, E1.
  destruct (ibis_val γ 0) eqn:H0, (ibis_val γ 1) eqn:H1; try reflexivity.
  - exfalso.
    pose (nγ := pcompose (pdisc_mor bool_setoid_object@{o o} PBool
                            swap_set@{o}) γ).
    apply (ibis_contra nγ).
    + unfold ibis_val in *. simpl. rewrite H0. reflexivity.
    + unfold ibis_val in *. simpl. rewrite H1. reflexivity.
  - exfalso. exact (ibis_contra γ H0 H1).
Qed.

(** ** Straight-line paths *)

(* Multiplication real absolute value at most one carries ball
 进入 ball same radius. （已译） *)
Lemma rball_scale@{} (x r s : CReal) (e : Q) :
  CRealLe (CReal_abs x) (inject_Q 1) → rball r s e →
  rball (CReal_mult r x) (CReal_mult s x) e.
Proof.
  unfold rball; intros Hx b.
  assert (E : CRealEq (CReal_minus (CReal_mult s x) (CReal_mult r x))
                      (CReal_mult (CReal_minus s r) x)).
  { unfold CReal_minus. ring. }
  rewrite E, CReal_abs_mult.
  apply (CReal_le_trans _
           (CReal_mult (CReal_abs (CReal_minus s r)) (inject_Q 1))).
  - apply CReal_mult_le_compat_l; [apply CReal_abs_pos|exact Hx].
  - rewrite CReal_mult_1_r. exact b.
Qed.

Program Definition line_scale@{o} (x : CReal) :
  SetoidMorphism@{o o o} RLine_setoid@{o} RLine_setoid@{o} := {|
  morphism := fun r => CReal_mult r x
|}.
Next Obligation. intros x r s H; simpl in *. rewrite H. reflexivity. Qed.

Lemma pline_scale_cont@{o} (x : CReal)
  (Hx : CRealLe (CReal_abs x) (inject_Q 1)) :
  @PCont PRLine@{o} PRLine@{o} (line_scale@{o} x).
Proof.
  intros U HU r u. destruct (HU _ u) as [e [He Hb]].
  exists e. split; [exact He|].
  intros s b. apply Hb. exact (rball_scale x r s e Hx b).
Qed.

Definition pline_scale@{o} (x : CReal)
  (Hx : CRealLe (CReal_abs x) (inject_Q 1)) :
  PMor@{o} PRLine@{o} PRLine@{o} :=
  @Build_PMor PRLine PRLine (line_scale x) (pline_scale_cont x Hx).

Lemma ival_abs_le@{o} (a : IvalSetoid@{o}) :
  CRealLe (CReal_abs (proj1_sig a)) (inject_Q 1).
Proof.
  destruct a as [a [H0 H1]]; simpl.
  rewrite (CReal_abs_right a H0). exact H1.
Qed.

Lemma ival_mult_pred@{} (t a : CReal) :
  ival_pred t → ival_pred a → ival_pred (CReal_mult t a).
Proof.
  intros [Ht0 Ht1] [Ha0 Ha1]. split.
  - apply CReal_mult_le_0_compat; [exact Ht0|exact Ha0].
  - rewrite CReal_mult_comm.
    apply (CReal_le_trans _ (CReal_mult a (inject_Q 1))).
    + apply CReal_mult_le_compat_l; [exact Ha0|exact Ht1].
    + rewrite CReal_mult_1_r. exact Ha1.
Qed.

Program Definition ival_scale_map@{o} (a : IvalSetoid@{o}) :
  SetoidMorphism@{o o o} IvalSetoid@{o} IvalSetoid@{o} := {|
  morphism := fun t =>
    exist _ (CReal_mult (proj1_sig t) (proj1_sig a))
      (ival_mult_pred _ _ (proj2_sig t) (proj2_sig a))
|}.
Next Obligation. intros a t s H; simpl in *. rewrite H. reflexivity. Qed.

(* The segment 0 [a], t ↦ t·a, path interval: continuous
 because 复合 含入 scaling line. （已译） *)
Definition ival_segment@{o} (a : IvalSetoid@{o}) :
  PMor@{o} PInterval@{o} PInterval@{o} :=
  psub_lift PRLine@{o} IvalSetoid@{o} ival_incl@{o} PInterval@{o}
    (pcompose (pline_scale (proj1_sig a) (ival_abs_le a))
       (psub_incl PRLine@{o} IvalSetoid@{o} ival_incl@{o}))
    (ival_scale_map a) (fun t => CRealEq_refl _).

Example ival_segment_map@{o} (a t : IvalSetoid@{o}) :
  proj1_sig (pmap (ival_segment@{o} a) t)
    = CReal_mult (proj1_sig t) (proj1_sig a) := eq_refl.

Lemma ival_segment_0@{o} (a : IvalSetoid@{o}) :
  pmap (ival_segment@{o} a) ival_zero@{o} ≈ ival_zero@{o}.
Proof. simpl. apply CReal_mult_0_l. Qed.

Lemma ival_segment_1@{o} (a : IvalSetoid@{o}) :
  pmap (ival_segment@{o} a) ival_one@{o} ≈ a.
Proof. simpl. apply CReal_mult_1_l. Qed.

(* Every continuous map interval [PBool] 常值:
 [interval_bool_endpoints] along segment 0 each point. （已译） *)
Theorem interval_bool_constant@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (s t : IvalSetoid@{o}) : pmap γ s = pmap γ t.
Proof.
  assert (H : ∀ a : IvalSetoid@{o}, pmap γ ival_zero = pmap γ a).
  { intro a.
    pose proof (interval_bool_endpoints (pcompose γ (ival_segment a))) as E.
    transitivity (pmap γ (pmap (ival_segment a) ival_zero)).
    - apply (proper_morphism (pmap γ)). symmetry. apply ival_segment_0.
    - transitivity (pmap γ (pmap (ival_segment a) ival_one)); [exact E|].
      apply (proper_morphism (pmap γ)). apply ival_segment_1. }
  rewrite <- (H s). exact (H t).
Qed.

(* The same statement, as Instance/Top/Components.v's two-point form of
   connectedness. *)
Definition interval_PConnectedBool@{o} : PConnectedBool PInterval@{o} :=
  interval_bool_constant@{o}.

(* 相关说明。 （已译） *)

Lemma pinterval_point_rel@{o so p | o < so, p <= o +}
  (x : PMor@{o} PPoint@{o} PInterval@{o}) :
  colim_rel (PPathPair_obj@{o so p} PInterval@{o})
    (existT _ ParY ival_end0@{o}) (existT _ ParY x).
Proof.
  set (a := pmap x ttt).
  refine (cr_trans (PPathPair_obj PInterval) _
            (existT _ ParY (pcompose (ival_segment a) ival_end0)) _ _ _).
  - apply (cr_point (PPathPair_obj PInterval) ParY).
    intro u; simpl. symmetry. apply CReal_mult_0_l.
  - refine (cr_trans (PPathPair_obj PInterval) _
              (existT _ ParX (ival_segment a)) _ _ _).
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj PInterval) ParX ParY
                                   (true; ParOne) (ival_segment a))).
    + refine (cr_trans (PPathPair_obj PInterval) _
                (existT _ ParY (pcompose (ival_segment a) ival_end1))
                _ _ _).
      * exact (cr_glue (PPathPair_obj PInterval) ParX ParY
                       (false; ParTwo) (ival_segment a)).
      * apply (cr_point (PPathPair_obj PInterval) ParY).
        intros []. exact (ival_segment_1 a).
Qed.

Lemma pinterval_rel@{o so p | o < so, p <= o +}
  (c : colim_obj PathColim@{o so p}
         (PPathPair_obj@{o so p} PInterval@{o})) :
  colim_rel (PPathPair_obj@{o so p} PInterval@{o})
    (existT _ ParY ival_end0@{o}) c.
Proof.
  destruct c as [[] x].
  - refine (cr_trans (PPathPair_obj PInterval) _
              (existT _ ParY (pcompose x ival_end0)) _ _ _).
    + exact (pinterval_point_rel _).
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj PInterval) ParX ParY
                                   (true; ParOne) x)).
  - exact (pinterval_point_rel x).
Qed.

Program Definition PPi0_PInterval_iso@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PInterval@{o} ≅[Sets@{o so}] unit_setoid_object@{o o}
  := {|
  to   := {| morphism := fun _ => ttt |};
  from := {| morphism := fun _ => existT _ ParY ival_end0@{o} |}
|}.
Next Obligation. intros c d _; reflexivity. Qed.
Next Obligation. intros u v _; apply colim_rel_refl. Qed.
Next Obligation. intros []; reflexivity. Qed.
Next Obligation. intro c. exact (pinterval_rel c). Qed.

(* 相关说明。 （已译） *)

Program Definition pbool_at_zero@{o so | o < so +} :
  PHomSetoid@{o} PInterval@{o} PBool@{o} ~{Sets@{o so}}~>
  bool_setoid_object@{o o} := {|
  morphism := fun q => pmap q ival_zero@{o}
|}.
Next Obligation. intros q r H. exact (H _). Qed.

Program Definition pbool_at_point@{o so | o < so +} :
  PHomSetoid@{o} PPoint@{o} PBool@{o} ~{Sets@{o so}}~>
  bool_setoid_object@{o o} := {|
  morphism := fun x => pmap x ttt
|}.
Next Obligation. intros x y H. exact (H _). Qed.

(* 相关说明。 （已译） *)
Definition pi0_bool_cocone@{o so p | o < so, p <= o +} :
  Cocone (PPathPair_obj@{o so p} PBool@{o}).
Proof.
  unshelve refine (@Cocone_of _ _ (PPathPair_obj PBool) bool_setoid_object
    (fun j => match j with
              | ParX => pbool_at_zero
              | ParY => pbool_at_point
              end) _).
  intros [] [] [[] f] q; simpl;
    first [ reflexivity
          | exact (False_rect _ (ParHom_Y_X_absurd _ f))
          | exact (False_rect _ (ParHom_Id_false_absurd _ f))
          | idtac ].
  exact (interval_bool_constant q ival_one ival_zero).
Defined.

(* 相关说明。 （已译） *)
Theorem Pi0_PBool_two@{o so p f | o < so, p <= o, o < f +} :
  @equiv _ (fobj[PPi0@{o so p f}] PBool@{o})
    (colim_inj PathColim@{o so p} (PPathPair_obj@{o so p} PBool@{o}) ParY
       ppoint_true@{o})
    (colim_inj PathColim@{o so p} (PPathPair_obj@{o so p} PBool@{o}) ParY
       ppoint_false@{o}) → False.
Proof.
  intro H.
  pose proof (proper_morphism
                (colim_med PathColim pi0_bool_cocone) _ _ H) as H'.
  exact (PBool_points_distinct (eq_sym H')).
Qed.

Program Definition PPi0_PBool_iso@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PBool@{o} ≅[Sets@{o so}] bool_setoid_object@{o o}
  := {|
  to   := colim_med PathColim@{o so p} pi0_bool_cocone@{o so p};
  from := {| morphism := fun b =>
               existT _ ParY (ppoint_at@{o} PBool@{o} b) |}
|}.
Next Obligation. intros b c H; simpl in H; subst; apply colim_rel_refl. Qed.
Next Obligation. intro b; reflexivity. Qed.
Next Obligation.
  intros [[] x]; simpl.
  - refine (cr_trans (PPathPair_obj PBool) _
              (existT _ ParY (pcompose x ival_end0)) _ _ _).
    + apply (cr_point (PPathPair_obj PBool) ParY). intro u; reflexivity.
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj PBool) ParX ParY
                                   (true; ParOne) x)).
  - apply (cr_point (PPathPair_obj PBool) ParY). intros []; reflexivity.
Qed.
