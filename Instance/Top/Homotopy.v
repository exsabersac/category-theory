Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Construction.Quotient.

Generalizable All Variables.

Open Scope R_scope.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(* * * Homotopy, homotopy 范畴, pointed forms （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/homotopy+category
   nLab:      https://ncatlab.org/nlab/show/homotopy
   nLab:      https://ncatlab.org/nlab/show/pointed+topological+space
   Wikipedia: https://en.wikipedia.org/wiki/Homotopy_category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Mac Lane, ibid., §II.8 "Quotient Categories", printed p. 51
   Book:      Riehl, "Category Theory in Context", §1.1 Exercise 1.1.iv,

   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Homotopy of continuous maps *)

Record Homotopy {X Y : TopSpace} (f g : X ~{Top}~> Y) := {
  htpy_map :> X → Ipt → Y;

  htpy_proper : ∀ (x x' : X) (t t' : Ipt),
    x ≈ x' → ival t = ival t' → htpy_map x t ≈ htpy_map x' t';

  htpy_cont : ∀ V : Y → Type, IsOpen Y V →
    ∀ (x : X) (t : Ipt), V (htpy_map x t) →
      { r : R & ((0 < r) ∧
        { U : X → Type & ((IsOpen X U) ∧ (U x) ∧
          (∀ (y : X) (s : Ipt),
             U y → Rabs (ival t - ival s) < r →
             V (htpy_map y s)))%type })%type };

  htpy_zero : ∀ x : X, htpy_map x I_zero ≈ f x;
  htpy_one : ∀ x : X, htpy_map x I_one ≈ g x
}.

Arguments htpy_map {X Y f g} _ _ _.
Arguments htpy_proper {X Y f g} _ _ _ _ _ _ _.
Arguments htpy_cont {X Y f g} _ _ _ _ _ _.
Arguments htpy_zero {X Y f g} _ _.
Arguments htpy_one {X Y f g} _ _.

(* * ** Reflexivity: 常值 homotopy （已译） *)

Definition homotopy_const {X Y : TopSpace} {f g : X ~{Top}~> Y}
           (E : f ≈ g) : Homotopy f g.
Proof.
  refine {| htpy_map := fun (x : X) (_ : Ipt) => f x |}.
  - intros x x' t t' Hx _.
    exact (proper_morphism f x x' Hx).
  - intros V HV x t Vx.
    exists 1; split; [ lra | ].
    exists (fun y => V (f y)); split; [ | split ].
    + exact (continuity f V HV).
    + exact Vx.
    + intros y s Uy _; exact Uy.
  - intro x; reflexivity.
  - exact E.
Defined.

(* 相关说明。 （已译） *)

Definition homotopy_sym {X Y : TopSpace} {f g : X ~{Top}~> Y}
           (H : Homotopy f g) : Homotopy g f.
Proof.
  refine {| htpy_map := fun (x : X) (t : Ipt) => htpy_map H x (I_rev t) |}.
  - intros x x' t t' Hx Ht.
    apply (htpy_proper H); [ exact Hx | ].
    rewrite !I_rev_eval, Ht; reflexivity.
  - intros V HV x t Vx.
    destruct (htpy_cont H V HV x (I_rev t) Vx)
      as [r [Hr [U [HU [Ux Hball]]]]].
    exists r; split; [ exact Hr | ].
    exists U; split; [ exact HU | split; [ exact Ux | ] ].
    intros y s Uy Hs.
    apply (Hball y (I_rev s) Uy).
    rewrite !I_rev_eval.
    revert Hs; Rlin.
  - intro x.
    transitivity (htpy_map H x I_one); [ | exact (htpy_one H x) ].
    apply (htpy_proper H); [ reflexivity | ].
    rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
  - intro x.
    transitivity (htpy_map H x I_zero); [ | exact (htpy_zero H x) ].
    apply (htpy_proper H); [ reflexivity | ].
    rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
Defined.

(* 相关说明。 （已译） *)

Section HomotopyTrans.

Context {X Y : TopSpace}.
Context {f g h : X ~{Top}~> Y}.
Context (H1 : Homotopy f g).
Context (H2 : Homotopy g h).

(*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition htrans_fun (x : X) (t : Ipt) : Y :=
  if Rle_dec (ival t) (1/2)
  then htpy_map H1 x (I_dbl t)
  else htpy_map H2 x (I_dbl' t).

Lemma htrans_left (x : X) (t : Ipt) :
  ival t <= 1/2 → htrans_fun x t = htpy_map H1 x (I_dbl t).
Proof.
  intro Ht; unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - reflexivity.
  - exfalso; exact (Hnle Ht).
Qed.

Lemma htrans_right (x : X) (t : Ipt) :
  1/2 < ival t → htrans_fun x t = htpy_map H2 x (I_dbl' t).
Proof.
  intro Ht; unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - exfalso; lra.
  - reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma htrans_agree (x : X) (t : Ipt) : ival t = 1/2 →
  htpy_map H1 x (I_dbl t) ≈ htpy_map H2 x (I_dbl' t).
Proof.
  intro Ht.
  transitivity (g x).
  - transitivity (htpy_map H1 x I_one); [ | exact (htpy_one H1 x) ].
    apply (htpy_proper H1); [ reflexivity | ].
    rewrite I_dbl_eval, ival_I_one, Ht; Rlin.
  - symmetry.
    transitivity (htpy_map H2 x I_zero); [ | exact (htpy_zero H2 x) ].
    apply (htpy_proper H2); [ reflexivity | ].
    rewrite I_dbl'_eval, ival_I_zero, Ht; Rlin.
Qed.

Lemma htrans_proper (x x' : X) (t t' : Ipt) :
  x ≈ x' → ival t = ival t' → htrans_fun x t ≈ htrans_fun x' t'.
Proof.
  intros Hx Ht; unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle],
           (Rle_dec (ival t') (1/2)) as [Hle' | Hnle'].
  - apply (htpy_proper H1); [ exact Hx | ].
    rewrite !I_dbl_eval, Ht; reflexivity.
  - exfalso; apply Hnle'; lra.
  - exfalso; apply Hnle; lra.
  - apply (htpy_proper H2); [ exact Hx | ].
    rewrite !I_dbl'_eval, Ht; reflexivity.
Qed.

(*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma htrans_cont (V : Y → Type) (HV : IsOpen Y V) (x : X) (t : Ipt) :
  V (htrans_fun x t) →
  { r : R & ((0 < r) ∧
    { U : X → Type & ((IsOpen X U) ∧ (U x) ∧
      (∀ (y : X) (s : Ipt),
         U y → Rabs (ival t - ival s) < r →
         V (htrans_fun y s)))%type })%type }.
Proof.
  intro Vx.
  destruct (total_order_T (ival t) (1/2)) as [[Hlt | Heq] | Hgt].
  - (* strictly inside the first half *)
    assert (Ht2 : ival t <= 1/2) by lra.
    rewrite (htrans_left x t Ht2) in Vx.
    destruct (htpy_cont H1 V HV x (I_dbl t) Vx)
      as [r [Hr [U [HU [Ux Hb]]]]].
    exists (Rmin (r/2) (1/2 - ival t)); split; [ Rlin | ].
    exists U; split; [ exact HU | split; [ exact Ux | ] ].
    intros y s Uy Hs.
    assert (Hs2 : ival s <= 1/2) by (revert Hs; Rlin).
    rewrite (htrans_left y s Hs2).
    apply (Hb y (I_dbl s) Uy).
    rewrite !I_dbl_eval.
    revert Hs; Rlin.
  - (* 相关说明。 （已译） *)
    assert (Ht2 : ival t <= 1/2) by lra.
    rewrite (htrans_left x t Ht2) in Vx.
    assert (Vx2 : V (htpy_map H2 x (I_dbl' t)))
      by exact (open_proper Y V HV _ _ (htrans_agree x t Heq) Vx).
    destruct (htpy_cont H1 V HV x (I_dbl t) Vx)
      as [r1 [Hr1 [U1 [HU1 [Ux1 Hb1]]]]].
    destruct (htpy_cont H2 V HV x (I_dbl' t) Vx2)
      as [r2 [Hr2 [U2 [HU2 [Ux2 Hb2]]]]].
    exists (Rmin (r1/2) (r2/2)); split; [ Rlin | ].
    exists (fun y => U1 y ∧ U2 y); split;
      [ exact (open_inter X U1 U2 HU1 HU2)
      | split; [ exact (Ux1, Ux2) | ] ].
    intros y s Uy Hs.
    destruct (Rle_dec (ival s) (1/2)) as [Hle | Hnle].
    + rewrite (htrans_left y s Hle).
      apply (Hb1 y (I_dbl s) (fst Uy)).
      rewrite !I_dbl_eval.
      revert Hs; rewrite Heq; Rlin.
    + apply Rnot_le_lt in Hnle.
      rewrite (htrans_right y s Hnle).
      apply (Hb2 y (I_dbl' s) (snd Uy)).
      rewrite !I_dbl'_eval.
      revert Hs; rewrite Heq; Rlin.
  - (* strictly inside the second half *)
    rewrite (htrans_right x t Hgt) in Vx.
    destruct (htpy_cont H2 V HV x (I_dbl' t) Vx)
      as [r [Hr [U [HU [Ux Hb]]]]].
    exists (Rmin (r/2) (ival t - 1/2)); split; [ Rlin | ].
    exists U; split; [ exact HU | split; [ exact Ux | ] ].
    intros y s Uy Hs.
    assert (Hs2 : 1/2 < ival s) by (revert Hs; Rlin).
    rewrite (htrans_right y s Hs2).
    apply (Hb y (I_dbl' s) Uy).
    rewrite !I_dbl'_eval.
    revert Hs; Rlin.
Defined.

Definition homotopy_trans : Homotopy f h.
Proof.
  refine {| htpy_map := htrans_fun |}.
  - exact htrans_proper.
  - exact htrans_cont.
  - intro x.
    assert (Hz : ival I_zero <= 1/2) by (rewrite ival_I_zero; lra).
    rewrite (htrans_left x I_zero Hz).
    transitivity (htpy_map H1 x I_zero); [ | exact (htpy_zero H1 x) ].
    apply (htpy_proper H1); [ reflexivity | ].
    rewrite I_dbl_eval, ival_I_zero; Rlin.
  - intro x.
    assert (Ho : 1/2 < ival I_one) by (rewrite ival_I_one; lra).
    rewrite (htrans_right x I_one Ho).
    transitivity (htpy_map H2 x I_one); [ | exact (htpy_one H2 x) ].
    apply (htpy_proper H2); [ reflexivity | ].
    rewrite I_dbl'_eval, ival_I_one; Rlin.
Defined.

(* 相关说明。 （已译） *)
Lemma htrans_eval (x : X) (t : Ipt) :
  htpy_map homotopy_trans x t = htrans_fun x t.
Proof. reflexivity. Qed.

End HomotopyTrans.

(* * ** Compatibility 复合 （已译） *)

Section HomotopyComp.

Context {X Y Z : TopSpace}.
Context {f f' : Y ~{Top}~> Z}.
Context {g g' : X ~{Top}~> Y}.
Context (H1 : Homotopy f f').
Context (H2 : Homotopy g g').

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hcomp_fun (x : X) (t : Ipt) : Z :=
  htpy_map H1 (htpy_map H2 x t) t.

Definition homotopy_comp : Homotopy (f ∘ g) (f' ∘ g').
Proof.
  refine {| htpy_map := hcomp_fun |}.
  - intros x x' t t' Hx Ht; unfold hcomp_fun.
    apply (htpy_proper H1); [ | exact Ht ].
    exact (htpy_proper H2 x x' t t' Hx Ht).
  - intros V HV x t Vx; unfold hcomp_fun in *.
    (* 相关说明。 （已译） *)
    destruct (htpy_cont H1 V HV (htpy_map H2 x t) t Vx)
      as [r1 [Hr1 [U1 [HU1 [Ux1 Hb1]]]]].
    (* ... which is exactly what the inner certificate consumes *)
    destruct (htpy_cont H2 U1 HU1 x t Ux1)
      as [r2 [Hr2 [U2 [HU2 [Ux2 Hb2]]]]].
    exists (Rmin r1 r2); split; [ Rlin | ].
    exists U2; split; [ exact HU2 | split; [ exact Ux2 | ] ].
    intros y s Uy Hs.
    apply (Hb1 (htpy_map H2 y s) s).
    + apply (Hb2 y s Uy); revert Hs; Rlin.
    + revert Hs; Rlin.
  - intro x.
    transitivity (htpy_map H1 (g x) I_zero).
    + apply (htpy_proper H1); [ exact (htpy_zero H2 x) | reflexivity ].
    + exact (htpy_zero H1 (g x)).
  - intro x.
    transitivity (htpy_map H1 (g' x) I_one).
    + apply (htpy_proper H1); [ exact (htpy_one H2 x) | reflexivity ].
    + exact (htpy_one H1 (g' x)).
Defined.

Lemma hcomp_eval (x : X) (t : Ipt) :
  htpy_map homotopy_comp x t = hcomp_fun x t.
Proof. reflexivity. Qed.

End HomotopyComp.

(* 相关说明。 （已译） *)

(* The 关系 itself, at [HomRelT] -- [Type]-valued family of
 Construction/Quotient.v, so chosen homotopy DATA nothing is
 truncated away. （已译） *)
Definition homotopic : HomRelT Top :=
  fun (X Y : TopSpace) (f g : X ~{Top}~> Y) => Homotopy f g.

#[export]
Instance homotopy_congruence : HomCongruence homotopic.
Proof.
  constructor.
  - intros W Z p q E; exact (homotopy_const E).
  - intros W Z p q H; exact (homotopy_sym H).
  - intros W Z p q r H H'; exact (homotopy_trans H H').
  - intros W Z V p p' q q' H H'; exact (homotopy_comp H H').
Defined.

(* 相关说明。 （已译） *)
Definition Toph : Category := Quotient Top homotopic.

Definition TophProj : Top ⟶ Toph :=
  @QuotientProj Top homotopic homotopy_congruence.

(* 相关说明。 （已译） *)
Definition TophProj_Full : Full TophProj :=
  @QuotientProj_Full Top homotopic homotopy_congruence.

Lemma TophProj_obj (X : TopSpace) : fobj[TophProj] X = X.
Proof. reflexivity. Qed.

(** ** Pointed spaces *)

(* 相关说明。 （已译） *)
Record PointedTop := {
  ptop_space :> TopSpace;
  ptop_pt : carrier (top_carrier ptop_space)
}.

Record PointedMap (X Y : PointedTop) := {
  ptop_map :> ptop_space X ~{Top}~> ptop_space Y;
  ptop_preserves : ptop_map (ptop_pt X) ≈ ptop_pt Y
}.

Arguments ptop_map {X Y} _.
Arguments ptop_preserves {X Y} _.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PointedMap_equiv_Equivalence {X Y : PointedTop} :
  Equivalence (fun p q : PointedMap X Y => ptop_map p ≈ ptop_map q).
Proof.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; symmetry; exact Hpq.
  - intros p q r Hpq Hqr.
    transitivity (ptop_map q); [ exact Hpq | exact Hqr ].
Qed.

#[export]
Instance PointedMap_Setoid {X Y : PointedTop} : Setoid (PointedMap X Y) := {|
  equiv := fun p q => ptop_map p ≈ ptop_map q;
  setoid_equiv := PointedMap_equiv_Equivalence
|}.

Definition ptop_id {X : PointedTop} : PointedMap X X.
Proof.
  refine {| ptop_map := @id Top (ptop_space X) |}.
  reflexivity.
Defined.

Definition ptop_compose {X Y Z : PointedTop}
           (p : PointedMap Y Z) (q : PointedMap X Y) : PointedMap X Z.
Proof.
  refine {| ptop_map := ptop_map p ∘[Top] ptop_map q |}.
  simpl.
  transitivity (ptop_map p (ptop_pt Y)).
  - apply proper_morphism; exact (ptop_preserves q).
  - exact (ptop_preserves p).
Defined.

Lemma ptop_compose_respects {X Y Z : PointedTop} :
  Proper (equiv ==> equiv ==> equiv) (@ptop_compose X Y Z).
Proof.
  intros p p' Hp q q' Hq x; simpl.
  transitivity (ptop_map p (ptop_map q' x)).
  - apply proper_morphism; exact (Hq x).
  - exact (Hp (ptop_map q' x)).
Qed.

(* Mac Lane's [Top_*].

       objects: pointed spaces          (a space with a chosen point)
        arrows: based continuous maps   (f (pt X) ≈ pt Y)
      identity: the identity map
   composition: composition of continuous maps *)
Program Definition Top_pointed : Category := {|
  obj     := PointedTop;
  hom     := PointedMap;
  homset  := @PointedMap_Setoid;
  id      := @ptop_id;
  compose := @ptop_compose;

  compose_respects := @ptop_compose_respects
|}.

(** ** Based homotopy *)

(*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record BasedHomotopy {X Y : PointedTop} (p q : X ~{Top_pointed}~> Y) := {
  bhtpy :> Homotopy (ptop_map p) (ptop_map q);
  bhtpy_base : ∀ t : Ipt, htpy_map bhtpy (ptop_pt X) t ≈ ptop_pt Y
}.

Arguments bhtpy {X Y p q} _.
Arguments bhtpy_base {X Y p q} _ _.

Definition based_const {X Y : PointedTop} {p q : X ~{Top_pointed}~> Y}
           (E : p ≈ q) : BasedHomotopy p q.
Proof.
  refine {| bhtpy := homotopy_const (f:=ptop_map p) (g:=ptop_map q) E |}.
  intro t; exact (ptop_preserves p).
Defined.

Definition based_sym {X Y : PointedTop} {p q : X ~{Top_pointed}~> Y}
           (H : BasedHomotopy p q) : BasedHomotopy q p.
Proof.
  refine {| bhtpy := homotopy_sym (bhtpy H) |}.
  intro t; exact (bhtpy_base H (I_rev t)).
Defined.

Definition based_trans {X Y : PointedTop} {p q r : X ~{Top_pointed}~> Y}
           (H : BasedHomotopy p q) (H' : BasedHomotopy q r) :
  BasedHomotopy p r.
Proof.
  refine {| bhtpy := homotopy_trans (bhtpy H) (bhtpy H') |}.
  intro t.
  rewrite (htrans_eval (bhtpy H) (bhtpy H')).
  unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - exact (bhtpy_base H (I_dbl t)).
  - exact (bhtpy_base H' (I_dbl' t)).
Defined.

Definition based_comp {X Y Z : PointedTop}
           {p p' : Y ~{Top_pointed}~> Z} {q q' : X ~{Top_pointed}~> Y}
           (H : BasedHomotopy p p') (H' : BasedHomotopy q q') :
  BasedHomotopy (p ∘ q) (p' ∘ q').
Proof.
  (* the ascription is what makes the two readings of the composite meet:
     [ptop_map (p ∘ q)] reduces to [ptop_map p ∘ ptop_map q], but only by
     conversion, which unification against a metavariable will not do *)
  refine {| bhtpy := (homotopy_comp (bhtpy H) (bhtpy H')
                       : Homotopy (ptop_map (p ∘ q))
                                  (ptop_map (p' ∘ q'))) |}.
  intro t.
  rewrite (hcomp_eval (bhtpy H) (bhtpy H')).
  unfold hcomp_fun.
  transitivity (htpy_map (bhtpy H) (ptop_pt Y) t).
  - apply (htpy_proper (bhtpy H)); [ exact (bhtpy_base H' t) | reflexivity ].
  - exact (bhtpy_base H t).
Defined.

Definition based_homotopic : HomRelT Top_pointed :=
  fun (X Y : PointedTop) (p q : X ~{Top_pointed}~> Y) => BasedHomotopy p q.

#[export]
Instance based_homotopy_congruence : HomCongruence based_homotopic.
Proof.
  constructor.
  - intros W Z p q E; exact (based_const E).
  - intros W Z p q H; exact (based_sym H).
  - intros W Z p q r H H'; exact (based_trans H H').
  - intros W Z V p p' q q' H H'; exact (based_comp H H').
Defined.

Definition Toph_pointed : Category := Quotient Top_pointed based_homotopic.

Definition Toph_pointed_Proj : Top_pointed ⟶ Toph_pointed :=
  @QuotientProj Top_pointed based_homotopic based_homotopy_congruence.

Definition Toph_pointed_Proj_Full : Full Toph_pointed_Proj :=
  @QuotientProj_Full Top_pointed based_homotopic based_homotopy_congruence.

(* 相关说明。 （已译） *)

(* The 常值 arrow, exactly [top_point]'s construction domain
 left free: preimage any open CONSTANT predicate, every
 常值 predicate open. （已译） *)
Definition top_const (X Y : TopSpace) (b : Y) : X ~{Top}~> Y :=
  Build_ContinuousMorphism X Y
    (const_morphism (top_carrier X) (top_carrier Y) b)
    (fun U _ => open_const X (U b)).

(*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ball_open_ball (A : BallSpace) (x : A) (d : R) :
  ball_open A (fun y => bdist x y < d).
Proof.
  intros z Hz.
  exists (d - bdist x z); split.
  - lra.
  - intros y Hy.
    pose proof (bdist_tri A x z y) as Htri.
    lra.
Qed.

(*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition homotopy_of_square {X : TopSpace} (F : Sq_Top ~{Top}~> X)
           (f g : I_Top ~{Top}~> X)
           (Hbot : ∀ t : Ipt, F (sq_pt t I_zero) ≈ f t)
           (Htop : ∀ t : Ipt, F (sq_pt t I_one) ≈ g t) : Homotopy f g.
Proof.
  (*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  unshelve refine (@Build_Homotopy I_Top X f g (fun x t => F (sq_pt x t))
                     _ _ _ _).
  - intros x x' t t' Hx Ht.
    apply Sqap; [ exact Hx | exact Ht ].
  - intros V HV x t Vx.
    destruct (continuity F V HV (sq_pt x t) Vx) as [d [Hd Hball]].
    exists d; split; [ exact Hd | ].
    exists (fun y => @bdist BS_I x y < d); split;
      [ exact (ball_open_ball BS_I x d) | split ].
    + rewrite (bdist_zero BS_I x x (reflexivity x)); exact Hd.
    + intros y s Uy Hs.
      apply Hball.
      simpl; unfold BSprod_dist; simpl.
      revert Uy Hs; simpl; Rlin.
  - exact Hbot.
  - exact Htop.
Defined.

(* 相关说明。 （已译） *)

(* The straight-line homotopy (x, t) ↦ (1 - t)·x, [Sq_hmap] of
 Instance/Top/Interval.v at 恒等 常值 0. Every
 estimate it needs already proved there. （已译） *)
Definition I_straight : Sq_Top ~{Top}~> I_Top :=
  Sq_hmap rf_id rf_zero 2 two_pos rf_id_lo rf_id_hi rf_zero_lo rf_zero_hi
          rf_id_lip rf_zero_lip.

Definition I_const_zero : I_Top ~{Top}~> I_Top := top_const I_Top I_Top I_zero.

Lemma I_straight_bottom (t : Ipt) :
  I_straight (sq_pt t I_zero) ≈ (@id Top I_Top) t.
Proof.
  (* the two sides stated reduced form: [lra] compares ATOMS,
 would not see through 恒等箭头 常值 one （已译） *)
  assert (H : ival (I_straight (sq_pt t I_zero)) = ival t).
  { unfold I_straight.
    rewrite Sq_hmap_eval, sq_pt_t, sq_pt_s, ival_I_zero.
    unfold rf_id, rf_zero; lra. }
  exact H.
Qed.

Lemma I_straight_top (t : Ipt) : I_straight (sq_pt t I_one) ≈ I_const_zero t.
Proof.
  assert (H : ival (I_straight (sq_pt t I_one)) = ival I_zero).
  { unfold I_straight.
    rewrite Sq_hmap_eval, sq_pt_t, sq_pt_s, ival_I_one, ival_I_zero.
    unfold rf_id, rf_zero; lra. }
  exact H.
Qed.

Definition interval_contraction : Homotopy (@id Top I_Top) I_const_zero :=
  homotopy_of_square I_straight (@id Top I_Top) I_const_zero
    I_straight_bottom I_straight_top.

(* The 恒等 interval 常值 map at 0 homotopic ... （已译） *)
Theorem interval_id_homotopic_const :
  homotopic I_Top I_Top (@id Top I_Top) I_const_zero.
Proof. exact interval_contraction. Qed.

(* 相关说明。 （已译） *)
Theorem interval_id_not_const : ((@id Top I_Top) ≈ I_const_zero) → False.
Proof.
  intro E.
  assert (Hval : ival I_one = ival I_zero) by exact (E I_one).
  rewrite ival_I_one, ival_I_zero in Hval.
  lra.
Qed.

(*
   本节说明 Homotopy 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Toph_identifies_id_and_const :
  @equiv _ (@homset Toph I_Top I_Top)
    (fmap[TophProj] (@id Top I_Top)) (fmap[TophProj] I_const_zero).
Proof. exact interval_contraction. Qed.

(** ** The same witness, based at 0 *)

Definition I_pointed : PointedTop := {|
  ptop_space := I_Top;
  ptop_pt    := I_zero
|}.

Definition I_pt_id : I_pointed ~{Top_pointed}~> I_pointed.
Proof.
  unshelve refine (@Build_PointedMap I_pointed I_pointed (@id Top I_Top) _).
  reflexivity.
Defined.

Definition I_pt_const : I_pointed ~{Top_pointed}~> I_pointed.
Proof.
  unshelve refine (@Build_PointedMap I_pointed I_pointed I_const_zero _).
  reflexivity.
Defined.

(* 相关说明。 （已译） *)
Lemma interval_contraction_based (t : Ipt) :
  htpy_map interval_contraction I_zero t ≈ I_zero.
Proof.
  assert (H : ival (I_straight (sq_pt I_zero t)) = ival I_zero).
  { unfold I_straight.
    rewrite Sq_hmap_eval, sq_pt_t, sq_pt_s, ival_I_zero.
    unfold rf_id, rf_zero; lra. }
  exact H.
Qed.

Definition interval_based_contraction : BasedHomotopy I_pt_id I_pt_const.
Proof.
  refine {| bhtpy := (interval_contraction
                       : Homotopy (ptop_map I_pt_id)
                                  (ptop_map I_pt_const)) |}.
  exact interval_contraction_based.
Defined.

Theorem I_pt_id_not_const : (I_pt_id ≈ I_pt_const) → False.
Proof. intro E; exact (interval_id_not_const E). Qed.

Theorem Toph_pointed_identifies_id_and_const :
  @equiv _ (@homset Toph_pointed I_pointed I_pointed)
    (fmap[Toph_pointed_Proj] I_pt_id) (fmap[Toph_pointed_Proj] I_pt_const).
Proof. exact interval_based_contraction. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明hom、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HomotopyEquivalence {X Y : TopSpace} (f : X ~{Top}~> Y) : Type :=
  { g : Y ~{Top}~> X &
    (homotopic Y Y (f ∘ g) (@id Top Y) ∧
     homotopic X X (g ∘ f) (@id Top X))%type }.

Definition homotopy_equivalence_Toph_iso {X Y : TopSpace} (f : X ~{Top}~> Y)
           (E : HomotopyEquivalence f) : X ≅[Toph] Y :=
  @Build_Isomorphism Toph X Y f (projT1 E)
    (fst (projT2 E)) (snd (projT2 E)).

Definition Toph_iso_homotopy_equivalence {X Y : TopSpace} (i : X ≅[Toph] Y) :
  HomotopyEquivalence (to i) :=
  (from i; (iso_to_from i, iso_from_to i)).

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example homotopy_equivalence_round {X Y : TopSpace}
        (f : X ~{Top}~> Y) (E : HomotopyEquivalence f) :
  Toph_iso_homotopy_equivalence (homotopy_equivalence_Toph_iso f E) = E.
Proof. destruct E as [g [a b]]; reflexivity. Qed.

Example Toph_iso_round {X Y : TopSpace} (i : X ≅[Toph] Y) :
  homotopy_equivalence_Toph_iso (to i) (Toph_iso_homotopy_equivalence i)
    = i.
Proof. reflexivity. Qed.

(* The capstone: interval contractible, so homotopy 范畴
 it IS point -- while [Top] it not, two 范畴 having
 same 对象 same arrows. （已译） *)
Theorem interval_contractible : HomotopyEquivalence (top_one I_Top).
Proof.
  exists (top_point I_Top I_zero).
  split.
  - apply cong_incl, top_one_unique.
  - apply (cong_trans (g := I_const_zero)).
    + apply cong_incl; intro x; reflexivity.
    + exact (homotopy_sym interval_contraction).
Defined.

Definition interval_iso_point_in_Toph : I_Top ≅[Toph] Point_Top :=
  homotopy_equivalence_Toph_iso (top_one I_Top) interval_contractible.

Theorem interval_not_iso_point_in_Top : I_Top ≅[Top] Point_Top → False.
Proof.
  intro i.
  apply interval_id_not_const.
  intro x.
  transitivity (from i (to i x)).
  - symmetry; exact (iso_from_to i x).
  - (* every point interval goes same place through the
 one-point space, so 复合 常值 （已译） *)
    assert (Hpt : from i (to i x) ≈ from i (to i I_zero))
      by (apply proper_morphism;
          destruct (continuous_map (to i) x), (continuous_map (to i) I_zero);
          reflexivity).
    transitivity (from i (to i I_zero)); [ exact Hpt | ].
    exact (iso_from_to i I_zero).
Qed.
