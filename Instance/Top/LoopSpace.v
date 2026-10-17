Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Instance.Top.FundamentalGroupoid.
Require Import Category.Instance.Top.Presheaf.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(* 相关说明。 （已译） *)

(*
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Paper:     Eckmann, Hilton, "Group-like structures in general categories
   Paper:     Eckmann, Hilton, "Structure maps in group theory", Fundamenta
   nLab:      https://ncatlab.org/nlab/show/topological+group
   nLab:      https://ncatlab.org/nlab/show/loop+space
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Wikipedia: https://en.wikipedia.org/wiki/Topological_group

   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Record HTopMonoid := {
  htm_space :> TopSpace;

  htm_unit : htm_space;
  htm_mult : htm_space → htm_space → htm_space;

  htm_mult_proper : Proper (equiv ==> equiv ==> equiv) htm_mult;

  htm_unit_left : ∀ x : htm_space, htm_mult htm_unit x ≈ x;
  htm_unit_right : ∀ x : htm_space, htm_mult x htm_unit ≈ x;

  htm_mult_cont : ∀ V : htm_space → Type, IsOpen htm_space V →
    ∀ x y : htm_space, V (htm_mult x y) →
      { U : htm_space → Type &
        ((IsOpen htm_space U) ∧ (U x) ∧
         { W : htm_space → Type &
           ((IsOpen htm_space W) ∧ (W y) ∧
            (∀ x' y' : htm_space,
               U x' → W y' → V (htm_mult x' y')))%type })%type }
}.

(* Mac Lane's named 对象: group [Top]. The inverse's continuity is
 stated ordinary preimage form, map one variable is
 available literally [Continuous]. （已译） *)
Record TopGroup := {
  tg_monoid :> HTopMonoid;

  tg_inv : tg_monoid → tg_monoid;

  tg_inv_proper : Proper (equiv ==> equiv) tg_inv;

  tg_inv_left : ∀ x : tg_monoid,
    htm_mult tg_monoid (tg_inv x) x ≈ htm_unit tg_monoid;
  tg_inv_right : ∀ x : tg_monoid,
    htm_mult tg_monoid x (tg_inv x) ≈ htm_unit tg_monoid;

  tg_inv_cont : ∀ V : tg_monoid → Type,
    IsOpen (htm_space tg_monoid) V →
    IsOpen (htm_space tg_monoid) (fun x => V (tg_inv x))
}.

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tg_inv_nbhd (G : TopGroup) (V : G → Type)
      (HV : IsOpen (htm_space (tg_monoid G)) V) (x : G) (Hx : V (tg_inv G x)) :
  { U : G → Type &
    ((IsOpen (htm_space (tg_monoid G)) U) ∧ (U x) ∧
     (∀ y : G, U y → V (tg_inv G y)))%type }.
Proof.
  exists (fun z => V (tg_inv G z)).
  split; [ | split ].
  - exact (tg_inv_cont G V HV).
  - exact Hx.
  - intros y Hy; exact Hy.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma open_of_nbhds (X : TopSpace) (P : X → Type)
      (H : ∀ x : X, P x →
             { U : X → Type &
               ((IsOpen X U) ∧ (U x) ∧ (∀ y : X, U y → P y))%type }) :
  IsOpen X P.
Proof.
  apply (open_respects X
           (fun x => { w : { z : X & P z } &
                       projT1 (H (projT1 w) (projT2 w)) x })
           P).
  - intro x; split.
    + intros [w Hw].
      exact (snd (snd (projT2 (H (projT1 w) (projT2 w)))) x Hw).
    + intro Px.
      exact ((x; Px); fst (snd (projT2 (H x Px)))).
  - apply open_union.
    intro w.
    exact (fst (projT2 (H (projT1 w) (projT2 w)))).
Qed.

(* * ** The pointwise product two arrows topological 幺半群 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section PointwiseProduct.

Context (G : HTopMonoid).
Context {D : TopSpace}.
Context (p q : D ~{Top}~> G).

Definition mult_fun (z : D) : G := htm_mult G (p z) (q z).

Lemma mult_fun_proper : Proper (equiv ==> equiv) mult_fun.
Proof.
  intros z w Hzw.
  apply (htm_mult_proper G); apply proper_morphism; exact Hzw.
Qed.

Definition mult_setoid_map : SetoidMorphism (top_carrier D) (top_carrier G) := {|
  morphism        := mult_fun;
  proper_morphism := mult_fun_proper
|}.

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mult_open (V : G → Type) (HV : IsOpen (htm_space G) V) :
  IsOpen D (fun z => V (mult_fun z)).
Proof.
  apply open_of_nbhds.
  intros z Hz.
  destruct (htm_mult_cont G V HV (p z) (q z) Hz)
    as [U [HU [Uz [W [HW [Wz Hprod]]]]]].
  exists (fun w : D => U (p w) ∧ W (q w)).
  split; [ | split ].
  - apply open_inter.
    + exact (continuity p U HU).
    + exact (continuity q W HW).
  - split; [ exact Uz | exact Wz ].
  - intros w Hw; exact (Hprod (p w) (q w) (fst Hw) (snd Hw)).
Qed.

Definition mult_arrow : D ~{Top}~> G := {|
  continuous_map := mult_setoid_map;
  continuity     := mult_open
|}.

(* 相关说明。 （已译） *)
Lemma mult_arrow_eval (z : D) : mult_arrow z ≈ htm_mult G (p z) (q z).
Proof. reflexivity. Qed.

End PointwiseProduct.

Arguments mult_fun G {D} p q z.
Arguments mult_arrow G {D} p q.

(* 相关说明。 （已译） *)

Section Loops.

Context (G : HTopMonoid).

(* 相关说明。 （已译） *)
Lemma loop_mult_src (p q : Path G (htm_unit G) (htm_unit G)) :
  mult_arrow G (path_map p) (path_map q) I_zero ≈ htm_unit G.
Proof.
  transitivity (htm_mult G (htm_unit G) (htm_unit G)).
  - apply (htm_mult_proper G); [ exact (path_src p) | exact (path_src q) ].
  - exact (htm_unit_left G (htm_unit G)).
Qed.

Lemma loop_mult_tgt (p q : Path G (htm_unit G) (htm_unit G)) :
  mult_arrow G (path_map p) (path_map q) I_one ≈ htm_unit G.
Proof.
  transitivity (htm_mult G (htm_unit G) (htm_unit G)).
  - apply (htm_mult_proper G); [ exact (path_tgt p) | exact (path_tgt q) ].
  - exact (htm_unit_left G (htm_unit G)).
Qed.

(* 相关说明。 （已译） *)
Definition loop_mult (p q : Path G (htm_unit G) (htm_unit G)) :
  Path G (htm_unit G) (htm_unit G) := {|
  path_map := mult_arrow G (path_map p) (path_map q);
  path_src := loop_mult_src p q;
  path_tgt := loop_mult_tgt p q
|}.

Lemma loop_mult_eval (p q : Path G (htm_unit G) (htm_unit G)) (t : Ipt) :
  path_map (loop_mult p q) t ≈ htm_mult G (path_map p t) (path_map q t).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition loop_mult_respects
           {p p' q q' : Path G (htm_unit G) (htm_unit G)}
           (H1 : PathHomotopy p p') (H2 : PathHomotopy q q') :
  PathHomotopy (loop_mult p q) (loop_mult p' q').
Proof.
  unfold PathHomotopy.
  refine {| ah_map := mult_arrow G (ah_map H1) (ah_map H2) |}.
  - intro t.
    apply (htm_mult_proper G); [ exact (ah_bot H1 t) | exact (ah_bot H2 t) ].
  - intro t.
    apply (htm_mult_proper G); [ exact (ah_top H1 t) | exact (ah_top H2 t) ].
  - intro s.
    transitivity (htm_mult G (htm_unit G) (htm_unit G)).
    + apply (htm_mult_proper G); [ exact (ah_left H1 s) | exact (ah_left H2 s) ].
    + exact (htm_unit_left G (htm_unit G)).
  - intro s.
    transitivity (htm_mult G (htm_unit G) (htm_unit G)).
    + apply (htm_mult_proper G);
        [ exact (ah_right H1 s) | exact (ah_right H2 s) ].
    + exact (htm_unit_left G (htm_unit G)).
Defined.

(* * ** The 常值 loop STRICT unit pointwise multiplication （已译） *)

(* 相关说明。 （已译） *)
Definition loop_mult_unit_left (p : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (const_path (htm_unit G)) p) p.
Proof.
  apply pointwise_homotopic.
  intro t.
  exact (htm_unit_left G (path_map p t)).
Defined.

Definition loop_mult_unit_right (p : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p (const_path (htm_unit G))) p.
Proof.
  apply pointwise_homotopic.
  intro t.
  exact (htm_unit_right G (path_map p t)).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem loop_interchange (a b c d : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (path_concat a b) (path_concat c d))
               (path_concat (loop_mult a c) (loop_mult b d)).
Proof.
  apply pointwise_homotopic.
  intro t.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - transitivity (path_map (loop_mult a c) (I_dbl t)).
    + apply (htm_mult_proper G).
      * apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
      * apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
    + symmetry.
      apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (loop_mult b d) (I_dbl' t)).
    + apply (htm_mult_proper G).
      * apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
      * apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
    + symmetry.
      apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition loops_eckmann_hilton :
  (const_path (htm_unit G) ≈ const_path (htm_unit G))
    ∧ (∀ a b, loop_mult a b ≈ path_concat a b)
    ∧ (∀ a b, loop_mult a b ≈ loop_mult b a)
    ∧ (∀ a b c, loop_mult (loop_mult a b) c ≈ loop_mult a (loop_mult b c)) :=
  @eckmann_hilton
    (Path G (htm_unit G) (htm_unit G))
    (Path_Setoid (htm_unit G) (htm_unit G))
    loop_mult (@path_concat G _ _ _)
    (const_path (htm_unit G)) (const_path (htm_unit G))
    (fun p p' E1 q q' E2 => loop_mult_respects E1 E2)
    (fun p p' E1 q q' E2 => path_concat_respects E1 E2)
    loop_mult_unit_left loop_mult_unit_right
    (fun p => unit_left_homotopy p) (fun p => unit_right_homotopy p)
    loop_interchange.

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The two operations agree up to homotopy. *)
Theorem loop_mult_concat_agree (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p q) (path_concat p q).
Proof.
  exact (fst (snd loops_eckmann_hilton) p q).
Qed.

(* Pointwise multiplication is commutative up to homotopy (the f-side
   conclusion). *)
Theorem loop_mult_comm (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p q) (loop_mult q p).
Proof.
  exact (fst (snd (snd loops_eckmann_hilton)) p q).
Qed.

(* Pointwise multiplication is associative up to homotopy. *)
Theorem loop_mult_assoc (p q r : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (loop_mult p q) r) (loop_mult p (loop_mult q r)).
Proof.
  exact (snd (snd (snd loops_eckmann_hilton)) p q r).
Qed.

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem loop_concat_comm (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (path_concat p q) (path_concat q p).
Proof.
  exact (@eh_g_comm
           (Path G (htm_unit G) (htm_unit G))
           (Path_Setoid (htm_unit G) (htm_unit G))
           loop_mult (@path_concat G _ _ _)
           (const_path (htm_unit G)) (const_path (htm_unit G))
           (fun a a' E1 b b' E2 => loop_mult_respects E1 E2)
           (fun a a' E1 b b' E2 => path_concat_respects E1 E2)
           loop_mult_unit_left loop_mult_unit_right
           (fun a => unit_left_homotopy a) (fun a => unit_right_homotopy a)
           loop_interchange p q).
Qed.

End Loops.

Arguments loop_mult {G} p q.
Arguments loop_interchange {G} a b c d.
Arguments loop_concat_comm {G} p q.

(* 相关说明。 （已译） *)

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pi1_topgroup_abelian (G : HTopMonoid)
        (p q : fundamental_group G (htm_unit G)) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (loop_concat_comm q p).
Qed.

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example pi1_mon_op_is_concat (G : HTopMonoid)
        (p q : fundamental_group G (htm_unit G)) :
  mon_op p q = path_concat q p := eq_refl.

Example pi1_mon_unit_is_const (G : HTopMonoid) :
  @mon_unit (fundamental_group G (htm_unit G)) = const_path (htm_unit G)
  := eq_refl.

(* Mac Lane §II.5 Exercise 6 as stated: the fundamental group of a
   topological group, at its unit, is abelian. *)
Corollary pi1_TopGroup_abelian (G : TopGroup)
          (p q : fundamental_group (tg_monoid G) (htm_unit (tg_monoid G))) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (pi1_topgroup_abelian (tg_monoid G) p q).
Qed.

(** ** Witness: the additive reals *)

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance R_Setoid.

(*
   本节说明 LoopSpace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma R_ball_open (c d : R) :
  (0 < d)%R → IsOpen R_Top (fun r : R => (Rabs (c - r) < d)%R).
Proof.
  intros Hd r Hr.
  exists (d - Rabs (c - r))%R; split.
  - lra.
  - intros y Hy; simpl in Hy.
    pose proof (Rabs_triang (c - r) (r - y)) as Ht.
    replace (c - r + (r - y))%R with (c - y)%R in Ht by ring.
    lra.
Qed.

Lemma R_plus_proper : Proper (equiv ==> equiv ==> equiv) Rplus.
Proof.
  intros a b Hab c d Hcd.
  assert (Ha : a = b :> R) by exact Hab.
  assert (Hc : c = d :> R) by exact Hcd.
  rewrite Ha, Hc.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma R_plus_cont (V : R_Top → Type) (HV : IsOpen R_Top V)
      (x y : R_Top) (Hxy : V (Rplus x y)) :
  { U : R_Top → Type &
    ((IsOpen R_Top U) ∧ (U x) ∧
     { W : R_Top → Type &
       ((IsOpen R_Top W) ∧ (W y) ∧
        (∀ x' y' : R_Top, U x' → W y' → V (Rplus x' y')))%type })%type }.
Proof.
  destruct (HV (Rplus x y) Hxy) as [d [Hd Hball]].
  exists (fun u : R => (Rabs (x - u) < d / 2)%R).
  split; [ | split ].
  - apply R_ball_open; lra.
  - replace (x - x)%R with 0%R by ring; rewrite Rabs_R0; lra.
  - exists (fun w : R => (Rabs (y - w) < d / 2)%R).
    split; [ | split ].
    + apply R_ball_open; lra.
    + replace (y - y)%R with 0%R by ring; rewrite Rabs_R0; lra.
    + intros u w Hu Hw.
      apply Hball.
      pose proof (Rabs_triang (x - u) (y - w)) as Ht.
      replace (x - u + (y - w))%R with (x + y - (u + w))%R in Ht by ring.
      simpl; lra.
Qed.

Definition R_TopMonoid : HTopMonoid := {|
  htm_space  := R_Top;
  htm_unit   := 0%R;
  htm_mult   := Rplus;

  htm_mult_proper := R_plus_proper;

  htm_unit_left  := Rplus_0_l;
  htm_unit_right := Rplus_0_r;

  htm_mult_cont := R_plus_cont
|}.

Lemma R_opp_proper : Proper (equiv ==> equiv) Ropp.
Proof.
  intros a b Hab.
  assert (Ha : a = b :> R) by exact Hab.
  rewrite Ha; reflexivity.
Qed.

(* Negation is continuous: the same radius works, negation being an
   isometry. *)
Lemma R_opp_cont (V : R_Top → Type) (HV : IsOpen R_Top V) :
  IsOpen R_Top (fun x : R => V (Ropp x)).
Proof.
  intros x Hx.
  destruct (HV (Ropp x) Hx) as [d [Hd Hball]].
  exists d; split; [ exact Hd | ].
  intros y Hy.
  apply Hball.
  simpl in *.
  replace (- x - - y)%R with (- (x - y))%R by ring.
  rewrite Rabs_Ropp.
  exact Hy.
Qed.

Definition R_TopGroup : TopGroup := {|
  tg_monoid := R_TopMonoid;

  tg_inv := Ropp;

  tg_inv_proper := R_opp_proper;

  tg_inv_left  := Rplus_opp_l;
  tg_inv_right := Rplus_opp_r;

  tg_inv_cont := R_opp_cont
|}.

(* 相关说明。 （已译） *)
Example R_unit_is_zero : htm_unit R_TopMonoid = 0%R := eq_refl.

Example R_mult_is_plus : htm_mult R_TopMonoid = Rplus := eq_refl.

Example R_inv_is_opp : tg_inv R_TopGroup = Ropp := eq_refl.

Example R_loop_mult_eval
        (p q : Path R_TopMonoid (htm_unit R_TopMonoid) (htm_unit R_TopMonoid))
        (t : Ipt) :
  path_map (loop_mult p q) t ≈ (path_map p t + path_map q t)%R.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Corollary pi1_R_abelian
          (p q : fundamental_group R_TopMonoid (htm_unit R_TopMonoid)) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (pi1_topgroup_abelian R_TopMonoid p q).
Qed.
