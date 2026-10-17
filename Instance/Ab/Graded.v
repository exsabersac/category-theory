(** * Graded abelian groups *)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.Discrete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/graded+object
 Wikipedia: https://en.wikipedia.org/wiki/Graded_(mathematics)

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The 范畴 graded abelian groups （已译） *)

(* Objects are ℕ-indexed families of abelian groups; an arrow is a
   homomorphism in each degree; everything is checked degreewise. *)
Program Definition GradedAb : Category := {|
  obj     := nat → AbObject;
  hom     := fun F G => ∀ n : nat, F n ~{Ab}~> G n;
  homset  := fun F G =>
    {| equiv := fun f g => ∀ n : nat, f n ≈ g n |};
  id      := fun F n => @id Ab (F n);
  compose := fun F G H f g n => f n ∘ g n
|}.
Next Obligation.
  intros F G; constructor.
  - intros f n; reflexivity.
  - intros f g Hfg n; symmetry; exact (Hfg n).
  - intros f g h H1 H2 n.
    transitivity (g n); [ exact (H1 n) | exact (H2 n) ].
Qed.
Next Obligation.
  (* [Ab]'s hom-setoid unfolds [CMonHom_Setoid], so ambient
 范畴 [Proper] instance has named. （已译） *)
  intros F G H f f' Hf g g' Hg n.
  exact (@compose_respects Ab (F n) (G n) (H n) _ _ (Hf n) _ _ (Hg n)).
Qed.
Next Obligation.
  intros F G f n; exact (id_left (f n)).
Qed.
Next Obligation.
  intros F G f n; exact (id_right (f n)).
Qed.
Next Obligation.
  intros F G H K f g h n; exact (comp_assoc (f n) (g n) (h n)).
Qed.
Next Obligation.
  intros F G H K f g h n; exact (comp_assoc_sym (f n) (g n) (h n)).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example graded_obj_definitional :
  obj[GradedAb] = obj[PiCat (fun _ : nat => Ab)] := eq_refl.

Example graded_hom_definitional (F G : obj[GradedAb]) :
  (F ~{GradedAb}~> G) = (F ~{PiCat (fun _ : nat => Ab)}~> G) := eq_refl.

Example graded_equiv_definitional (F G : obj[GradedAb]) :
  @equiv _ (@homset GradedAb F G)
    = @equiv _ (@homset (PiCat (fun _ : nat => Ab)) F G) := eq_refl.

Example graded_id_definitional (F : obj[GradedAb]) :
  @id GradedAb F = @id (PiCat (fun _ : nat => Ab)) F := eq_refl.

Example graded_compose_definitional (F G H : obj[GradedAb]) :
  @compose GradedAb F G H
    = @compose (PiCat (fun _ : nat => Ab)) F G H := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GradedAb_PiCat :
  GradedAb ⟶ PiCat (fun _ : nat => Ab) := {|
  fobj := fun F => F;
  fmap := fun F G f => f
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg n).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

Program Definition PiCat_GradedAb :
  PiCat (fun _ : nat => Ab) ⟶ GradedAb := {|
  fobj := fun F => F;
  fmap := fun F G f => f
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg n).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

(* Oriented towards [GradedAb], so it composes left the
 donor 同构 below. （已译） *)
Program Definition PiCat_GradedAb_iso :
  PiCat (fun _ : nat => Ab) ≅[Cat] GradedAb := {|
  to   := PiCat_GradedAb;
  from := GradedAb_PiCat
|}.
Next Obligation.
  exists (fun F => iso_id).
  intros F G f n; simpl; cat.
Qed.
Next Obligation.
  exists (fun F => iso_id).
  intros F G f n; simpl; cat.
Qed.

(** ** Mac Lane §II.4 Exercise 3 *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Graded_Fun_equiv :
  ([DiscreteCat nat, Ab]) ≅[Cat] GradedAb :=
  iso_compose PiCat_GradedAb_iso Fun_Discrete_PiCat.

(** ** The degree shift *)

(* Reindexing along successor: 自函子, since arrows are
 degreewise reindexing them needs no more than reindexing the
 对象. （已译） *)
Program Definition GradedAb_shift : GradedAb ⟶ GradedAb := {|
  fobj := fun F n => F (S n);
  fmap := fun F G f n => f (S n)
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg (S n)).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

(* Maps degree one not outside 范畴: they ordinary
 arrows 进入 shift, definitionally. （已译） *)
Example graded_degree_one (F G : obj[GradedAb]) :
  (∀ n : nat, F n ~{Ab}~> G (S n))
    = (F ~{GradedAb}~> fobj[GradedAb_shift] G) := eq_refl.

(** ** Witnesses *)

(* ℤ as an abelian group, through the ring layer: Instance/Rng.v's
   [ring_ab] applied to Theory/Algebra/Rig.v's axiom-free [Int_Ring],
   the same donor Instance/Ab/Monoidal.v uses for its unit object. *)
Definition Zgroup : AbObject := ring_ab Int_Ring.

(* Multiplication by a fixed integer, as an endomorphism of ℤ.  The
   [Proper] obligation of the underlying setoid morphism needs no
   proof: ℤ's setoid equivalence is Leibniz equality ([Z_eqT]), so
   elaboration discharges it. *)
Program Definition Zmul_hom (k : Z) : Zgroup ~{Ab}~> Zgroup := {|
  cmon_map := {| morphism := fun m => Z.mul k m |}
|}.
Next Obligation.
  intros k; simpl; exact (Z.mul_0_r k).
Qed.
Next Obligation.
  intros k a b; simpl; exact (Z.mul_add_distr_l k a b).
Qed.

(* The constant graded group ℤ in every degree. *)
Definition ConstZ : obj[GradedAb] := fun _ => Zgroup.

(* A genuinely graded endomorphism: multiplication by n in degree n.
   Its components differ from degree to degree — PROVED below
   ([graded_deg_mul_not_constant]), not asserted: no single
   homomorphism h has [graded_deg_mul] as its constant family. *)
Definition graded_deg_mul : ConstZ ~{GradedAb}~> ConstZ :=
  fun n => Zmul_hom (Z.of_nat n).

Lemma graded_deg_mul_not_constant
      (h : Zgroup ~{Ab}~> Zgroup) :
  (∀ n : nat, graded_deg_mul n ≈ h) → False.
Proof.
  intro Hc.
  pose proof (Hc 0%nat 5%Z) as H0.
  pose proof (Hc 1%nat 5%Z) as H1.
  simpl in H0, H1.
  rewrite <- H0 in H1.
  discriminate H1.
Qed.

Example graded_deg_mul_at_3 :
  cmon_map (graded_deg_mul 3%nat) 5%Z = 15%Z := eq_refl.

Example graded_deg_mul_at_0 :
  cmon_map (graded_deg_mul 0%nat) 5%Z = 0%Z := eq_refl.

(* 相关说明。 （已译） *)
Example shift_deg_mul_at_2 :
  cmon_map (fmap[GradedAb_shift] graded_deg_mul 2%nat) 5%Z = 15%Z := eq_refl.

(* A group concentrated degree zero — standard example a
 graded 对象 not 常值. （已译） *)
Definition conc0 : obj[GradedAb] :=
  fun n => match n with
           | O   => Zgroup
           | S _ => Ab_trivial
           end.

Example conc0_at_0 : conc0 0%nat = Zgroup := eq_refl.

(* 相关说明。 （已译） *)
Example shift_conc0_at_0 :
  fobj[GradedAb_shift] conc0 0%nat = Ab_trivial := eq_refl.

Example shift_conc0_at_3 :
  fobj[GradedAb_shift] conc0 3%nat = Ab_trivial := eq_refl.

(* 相关说明。 （已译） *)
Example shift_twice (F : obj[GradedAb]) (n : nat) :
  fobj[GradedAb_shift] (fobj[GradedAb_shift] F) n = F (S (S n)) := eq_refl.
