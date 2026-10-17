Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/abelianization

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition gcomm (G : GrpObject) (g h : carrier G) : carrier G :=
  grp_mul G (grp_mul G (grp_mul G g h) (grp_inv G g)) (grp_inv G h).

(* The commutator subgroup, as an ≈-saturated inductive generation. *)
Inductive InCommutator (G : GrpObject) : carrier G → Type :=
  | inc_comm (g h : carrier G) : InCommutator (gcomm G g h)
  | inc_unit : InCommutator (grp_unit G)
  | inc_mul (a b : carrier G) :
      InCommutator a → InCommutator b →
      InCommutator (grp_mul G a b)
  | inc_inv (a : carrier G) :
      InCommutator a → InCommutator (grp_inv G a)
  | inc_resp (a b : carrier G) :
      a ≈ b → InCommutator a → InCommutator b.

Arguments inc_comm {G} g h.
Arguments inc_unit {G}.
Arguments inc_mul {G a b} _ _.
Arguments inc_inv {G a} _.
Arguments inc_resp {G a b} _ _.

(* 相关说明。 （已译） *)
Lemma hom_commutator {G H : GrpObject} (f : GrpHom G H)
  (x : carrier G) : InCommutator G x → InCommutator H (grp_map f x).
Proof.
  intro Hx; induction Hx as
    [ g h | | a b Ha IHa Hb IHb | a Ha IHa | a b Hab Ha IHa ].
  - apply (inc_resp (a := gcomm H (grp_map f g) (grp_map f h))).
    + unfold gcomm.
      rewrite <- !(grp_map_inv f).
      rewrite <- !(grp_map_mul f).
      reflexivity.
    + apply inc_comm.
  - exact (inc_resp (symmetry (grp_map_unit f)) inc_unit).
  - exact (inc_resp (symmetry (grp_map_mul f a b)) (inc_mul IHa IHb)).
  - exact (inc_resp (symmetry (grp_map_inv f a)) (inc_inv IHa)).
  - exact (inc_resp (proper_morphism (grp_map f) a b Hab) IHa).
Qed.

(* Normality, as the conjugation instance. *)
Lemma conj_commutator (G : GrpObject) (t x : carrier G) :
  InCommutator G x →
  InCommutator G (grp_mul G (grp_mul G t x) (grp_inv G t)).
Proof. exact (hom_commutator (Grp_conj G t) x). Qed.

(* Homomorphisms abelian groups kill commutator elements — the
 descent germ (future) 伴随. （已译） *)
Lemma hom_to_abelian_kills {G H : GrpObject}
  (comm : ∀ a b : carrier H, grp_mul H a b ≈ grp_mul H b a)
  (f : GrpHom G H) (x : carrier G) :
  InCommutator G x → grp_map f x ≈ grp_unit H.
Proof.
  intro Hx; induction Hx as
    [ g h | | a b Ha IHa Hb IHb | a Ha IHa | a b Hab Ha IHa ].
  - unfold gcomm.
    rewrite !(grp_map_mul f), !(grp_map_inv f).
    rewrite (grp_mul_assoc H (grp_map f g) (grp_map f h)
               (grp_inv H (grp_map f g))).
    rewrite (comm (grp_map f h) (grp_inv H (grp_map f g))).
    rewrite <- (grp_mul_assoc H (grp_map f g) (grp_inv H (grp_map f g))
                  (grp_map f h)).
    rewrite (grp_mul_inv_r H (grp_map f g)).
    rewrite (grp_mul_unit_l H (grp_map f h)).
    apply (grp_mul_inv_r H).
  - apply (grp_map_unit f).
  - rewrite (grp_map_mul f a b).
    rewrite IHa, IHb.
    apply (grp_mul_unit_l H).
  - rewrite (grp_map_inv f a).
    rewrite IHa.
    apply (grp_inv_unit H).
  - now rewrite <- (proper_morphism (grp_map f) a b Hab).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Abelianization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CommutatorNS (G : GrpObject) : NormalSubgroup G :=
  {| ns_sub := {| sub_mem := InCommutator G
                ; sub_resp := fun a b Hab Ha => inc_resp Hab Ha
                ; sub_unit := inc_unit
                ; sub_mul := fun a b Ha Hb => inc_mul Ha Hb
                ; sub_inv := fun a Ha => inc_inv Ha |}
   ; ns_conj := fun t a Ha => conj_commutator G t a Ha |}.

(** ** The quotient relation *)

(*
   本节说明 Abelianization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition abel_eq (G : GrpObject) (a b : carrier G) : Prop :=
  inhabited (InCommutator G (grp_mul G a (grp_inv G b))).

(*
   本节说明 Abelianization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example abel_eq_is_quot_rel (G : GrpObject) (a b : carrier G) :
  abel_eq G a b = inhabited (quot_rel (CommutatorNS G) a b).
Proof. reflexivity. Qed.

(* The finer 关系 implies coarser one. （已译） *)
Lemma abel_eq_of_eq (G : GrpObject) (a b : carrier G) :
  a ≈ b → abel_eq G a b.
Proof. intro H; constructor; exact (quot_rel_of_equiv (CommutatorNS G) a b H). Qed.

Lemma abel_eq_refl (G : GrpObject) (a : carrier G) : abel_eq G a a.
Proof. constructor; exact (quot_rel_refl (CommutatorNS G) a). Qed.

Lemma abel_eq_sym (G : GrpObject) (a b : carrier G) :
  abel_eq G a b → abel_eq G b a.
Proof. intros [H]; constructor; exact (quot_rel_sym (CommutatorNS G) a b H). Qed.

Lemma abel_eq_trans (G : GrpObject) (a b c : carrier G) :
  abel_eq G a b → abel_eq G b c → abel_eq G a c.
Proof.
  intros [H1] [H2]; constructor.
  exact (quot_rel_trans (CommutatorNS G) a b c H1 H2).
Qed.

(* The operations respect quotient 关系; multiplication and
 inversion where normality earns keep. （已译） *)
Lemma abel_eq_mul (G : GrpObject) (a a' b b' : carrier G) :
  abel_eq G a a' → abel_eq G b b' →
  abel_eq G (grp_mul G a b) (grp_mul G a' b').
Proof.
  intros [H1] [H2]; constructor.
  exact (quot_rel_mul (CommutatorNS G) a a' b b' H1 H2).
Qed.

Lemma abel_eq_inv (G : GrpObject) (a a' : carrier G) :
  abel_eq G a a' → abel_eq G (grp_inv G a) (grp_inv G a').
Proof.
  intros [H]; constructor.
  exact (quot_rel_inv (CommutatorNS G) a a' H).
Qed.

(** ** The abelianization of a group *)

(*
   本节说明 Abelianization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition abel_setoid (G : GrpObject) : Setoid (carrier G) := {|
  equiv := abel_eq G
|}.
Next Obligation.
  intro G; equivalence.
  - apply abel_eq_refl.
  - now apply abel_eq_sym.
  - now apply (abel_eq_trans G x y).
Qed.

(* [abel_eq] IS [Prop] 关系, so quotient supplies own
 [cmon_prop] no 假设 taken anywhere. （已译） *)
Definition abel_PropEquiv (G : GrpObject) : PropEquiv (abel_setoid G) :=
  @PropEquiv_of_relation _ (abel_setoid G) (abel_eq G)
    (fun _ _ h => h) (fun _ _ h => h).

Program Definition AbelianizationOb (G : GrpObject) :
  AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := carrier G
                    ; is_setoid := abel_setoid G |};
    cmon_zero := grp_unit G;
    cmon_plus := grp_mul G;
    cmon_prop := abel_PropEquiv G
  |};
  ab_neg := grp_inv G
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; now apply abel_eq_mul.
Qed.
Next Obligation.
  intros G a b c; apply abel_eq_of_eq, grp_mul_assoc.
Qed.
Next Obligation.
  (* Commutativity IS the generating constructor. *)
  intros G a b; unfold abel_eq; constructor.
  apply (inc_resp (a := gcomm G a b)); [| apply inc_comm ].
  unfold gcomm.
  rewrite (grp_inv_mul G b a).
  rewrite (grp_mul_assoc G (grp_mul G a b) (grp_inv G a) (grp_inv G b)).
  reflexivity.
Qed.
Next Obligation.
  intros G a; apply abel_eq_of_eq, grp_mul_unit_l.
Qed.
Next Obligation.
  intros G a a' Ha; now apply abel_eq_inv.
Qed.
Next Obligation.
  intros G a; apply abel_eq_of_eq, grp_mul_inv_l.
Qed.

(* * ** The commutator subgroup, 函子 Grp ⟶ Grp （已译） *)

Definition commutator_carrier (G : GrpObject) : Type :=
  { x : carrier G & InCommutator G x }.

Definition mk_comm (G : GrpObject) (x : carrier G)
  (Hx : InCommutator G x) : commutator_carrier G :=
  existT (fun x : carrier G => InCommutator G x) x Hx.

(*
   本节说明 Abelianization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition commutator_setoid (G : GrpObject) : SetoidObject := {|
  carrier := commutator_carrier G;
  is_setoid := {| equiv := fun a b => `1 a ≈ `1 b |}
|}.
Next Obligation. intro G; equivalence; now transitivity (`1 y). Qed.

Program Definition CommutatorGrp (G : GrpObject) : GrpObject := {|
  grp_setoid := commutator_setoid G;
  grp_unit := mk_comm G (grp_unit G) inc_unit;
  grp_mul := fun a b =>
    mk_comm G (grp_mul G (`1 a) (`1 b)) (inc_mul (`2 a) (`2 b));
  grp_inv := fun a => mk_comm G (grp_inv G (`1 a)) (inc_inv (`2 a));
  (* The commutator subgroup's `≈` compares first projections in [G]. *)
  grp_prop :=
    sigma_first_PropEquiv (is_setoid (commutator_setoid G))
      (fun _ _ h => h) (fun _ _ h => h) (grp_prop G)
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *; now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

Program Definition Commutator_Functor : Grp ⟶ Grp := {|
  fobj := CommutatorGrp;
  fmap := fun G H (f : GrpHom G H) =>
    {| grp_map := {| morphism := fun a =>
         mk_comm H (grp_map f (`1 a)) (hom_commutator f (`1 a) (`2 a)) |}
    |}
|}.
Next Obligation.
  intros G H f a b Hab; simpl in *.
  exact (proper_morphism (grp_map f) _ _ Hab).
Qed.
Next Obligation. intros G H f; simpl; apply (grp_map_unit f). Qed.
Next Obligation. intros G H f a b; simpl; apply (grp_map_mul f). Qed.
Next Obligation.
  intros G H f g Hfg a; simpl.
  exact (Hfg (`1 a)).
Qed.
Next Obligation. intros G a; simpl; reflexivity. Qed.
Next Obligation. intros G H K f g a; simpl; reflexivity. Qed.

(** ** The inclusion Ab ⟶ Grp *)

Program Definition Ab_to_GrpOb (A : AbObject) : GrpObject := {|
  grp_setoid := cmon_setoid A;
  grp_unit := cmon_zero A;
  grp_mul := cmon_plus A;
  grp_inv := ab_neg A;
  (* 相关说明。 （已译） *)
  grp_prop := cmon_prop A
|}.
Next Obligation. intros A a b c; apply cmon_plus_assoc. Qed.
Next Obligation. intros A a; apply cmon_plus_zero_l. Qed.
Next Obligation. intros A a; apply ab_neg_left. Qed.

Program Definition Ab_to_Grp : Ab ⟶ Grp := {|
  fobj := Ab_to_GrpOb;
  fmap := fun A B (f : AbHom A B) =>
    {| grp_map := cmon_map f
     ; grp_map_unit := cmon_map_zero f
     ; grp_map_mul := cmon_map_plus f |}
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** ** The abelianization functor *)

Program Definition Abelianization_Functor : Grp ⟶ Ab := {|
  fobj := AbelianizationOb;
  fmap := fun G H (f : GrpHom G H) =>
    {| cmon_map := {| morphism := fun a : carrier G => grp_map f a |}
     |}
|}.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros G H f a b Hab; simpl in *.
  unfold abel_eq in *.
  destruct Hab as [Hab]; constructor.
  apply (inc_resp (a := grp_map f (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_map_mul f a (grp_inv G b)).
    rewrite (grp_map_inv f b).
    reflexivity.
  - exact (hom_commutator f _ Hab).
Qed.
Next Obligation.
  intros G H f; simpl.
  apply abel_eq_of_eq, (grp_map_unit f).
Qed.
Next Obligation.
  intros G H f a b; simpl.
  apply abel_eq_of_eq, (grp_map_mul f).
Qed.
Next Obligation.
  intros G H f g Hfg a; simpl.
  apply abel_eq_of_eq; exact (Hfg a).
Qed.
Next Obligation. intros G a; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros G H K f g a; simpl; apply abel_eq_refl. Qed.

(** ** The natural projection *)

(* The component at G: 恒等 function, read fine
 setoid 进入 coarse one. （已译） *)
Program Definition abel_proj (G : GrpObject) :
  G ~{Grp}~> Ab_to_GrpOb (AbelianizationOb G) := {|
  grp_map := {| morphism := fun a : carrier G => a |}
|}.
Next Obligation. intros G a b Hab; apply abel_eq_of_eq, Hab. Qed.
Next Obligation. intros G; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros G a b; simpl; apply abel_eq_refl. Qed.

(* Mac Lane's 自然性 square p_H ∘ f ≈ f' ∘ p_G, both legs the
 恒等 elements: reflexivity coarser 关系. （已译） *)
Program Definition abel_projection :
  @Id Grp ⟹ Ab_to_Grp ◯ Abelianization_Functor := {|
  transform := abel_proj
|}.
Next Obligation.
  intros G H f a; simpl; apply abel_eq_refl.
Qed.
Next Obligation.
  intros G H f a; simpl; apply abel_eq_refl.
Qed.

(** ** Non-degeneracy witnesses *)

(* 相关说明。 （已译） *)
Lemma commutator_GrpTwo_proper :
  InCommutator GrpTwo grp_two_one → False.
Proof.
  intro K.
  pose proof (hom_to_abelian_kills GrpTwo_abelian
                (@grp_hom_id GrpTwo) grp_two_one K) as E.
  exact E.
Qed.

(* In S₃ subgroup nontrivial: commutator two
 generators member not 恒等. （已译） *)
Lemma commutator_S3_nontrivial :
  InCommutator S3 (gcomm S3 S3_r S3_s) *
  (gcomm S3 S3_r S3_s ≈ s3_unit → False).
Proof.
  split.
  - apply inc_comm.
  - intro E; vm_compute in E; discriminate E.
Qed.

(* 相关说明。 （已译） *)
Lemma abelianization_S3_nontrivial :
  abel_eq S3 S3_s s3_unit → False.
Proof.
  intros [K].
  pose proof (hom_to_abelian_kills GrpTwo_abelian s3_sign _ K) as E.
  vm_compute in E.
  exact E.
Qed.
