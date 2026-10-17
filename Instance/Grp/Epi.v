Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(* Obligations discharged hand throughout, Instance/Grp.v, so that
 every 证明 below visible source rather than delegated a
 default tactic. （已译） *)
#[local] Obligation Tactic := idtac.

(* * * Epimorphisms 范畴 groups （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/epimorphisms+of+groups+are+surjective
 nLab: https://ncatlab.org/nlab/show/epimorphism

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Double-negation-stable types *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Stable (P : Type) : Type := ¬¬P → P.

Lemma stable_not (P : Type) : Stable (¬P).
Proof.
  intros HH p.
  apply HH.
  intro np.
  exact (np p).
Qed.

Lemma stable_not_not (P : Type) : Stable (¬¬P).
Proof. exact (stable_not (¬P)). Qed.

Lemma stable_arrow (P Q : Type) : Stable Q → Stable (P → Q).
Proof.
  intros HQ HH p.
  apply HQ.
  intro nq.
  apply HH.
  intro g.
  exact (nq (g p)).
Qed.

(* 相关说明。 （已译） *)
Lemma stable_and (P Q : Prop) : Stable P → Stable Q → Stable (P /\ Q).
Proof.
  intros HP HQ HH.
  split.
  - apply HP.
    intro np.
    apply HH.
    intros [p _].
    exact (np p).
  - apply HQ.
    intro nq.
    apply HH.
    intros [_ q].
    exact (nq q).
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StableProp : Type := ∃ P : Prop, Stable P.

Definition StableProp_equiv : crelation StableProp := λ P Q, `1 P ↔ `1 Q.

Lemma StableProp_equivalence : Equivalence StableProp_equiv.
Proof.
  unfold StableProp_equiv.
  constructor.
  - intro P.
    split; exact (λ x, x).
  - intros P Q [pq qp].
    split; assumption.
  - intros P Q R [pq qp] [qr rq].
    split.
    + exact (λ x, qr (pq x)).
    + exact (λ x, qp (rq x)).
Qed.

Definition StableSetoid : SetoidObject :=
  {| carrier   := StableProp
   ; is_setoid := {| equiv        := StableProp_equiv
                   ; setoid_equiv := StableProp_equivalence |} |}.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StableSetoid_PropEquiv : PropEquiv (is_setoid StableSetoid).
Proof.
  unshelve refine
    {| pequiv := fun P Q : StableProp => (`1 P -> `1 Q) /\ (`1 Q -> `1 P) |}.
  - intros P Q [pq qp]; split; assumption.
  - intros P Q [pq qp]; split; assumption.
Defined.

(** ** The image of a homomorphism *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GrpImage {G H : GrpObject} (f : G ~{Grp}~> H) (h : carrier H) : Type :=
  ∃ g : carrier G, grp_map f g ≈ h.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GrpSurjective {G H : GrpObject} (f : G ~{Grp}~> H) : Type :=
  ∀ h : carrier H, GrpImage f h.

Section Image.

Context {G H : GrpObject}.
Context (f : G ~{Grp}~> H).

Lemma GrpImage_respects (a b : carrier H) :
  a ≈ b → GrpImage f a → GrpImage f b.
Proof.
  intros Hab [g Hg].
  exists g.
  now rewrite Hg.
Qed.

Lemma GrpImage_unit : GrpImage f (grp_unit H).
Proof.
  exists (grp_unit G).
  apply (grp_map_unit f).
Qed.

Lemma GrpImage_mul (a b : carrier H) :
  GrpImage f a → GrpImage f b → GrpImage f (grp_mul H a b).
Proof.
  intros [ga Ha] [gb Hb].
  exists (grp_mul G ga gb).
  rewrite (grp_map_mul f).
  now rewrite Ha, Hb.
Qed.

Lemma GrpImage_inv (a : carrier H) :
  GrpImage f a → GrpImage f (grp_inv H a).
Proof.
  intros [g Hg].
  exists (grp_inv G g).
  rewrite (grp_map_inv f).
  now rewrite Hg.
Qed.

(** ** Left cosets of the image *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_coset_rel : crelation (carrier H) :=
  λ x y, GrpImage f (grp_mul H (grp_inv H y) x).

Lemma grp_coset_of_equiv (x y : carrier H) : x ≈ y → grp_coset_rel x y.
Proof.
  intro Hxy.
  unfold grp_coset_rel.
  apply (GrpImage_respects (grp_unit H)).
  - rewrite <- Hxy.
    symmetry.
    apply grp_mul_inv_l.
  - apply GrpImage_unit.
Qed.

Lemma grp_coset_refl (x : carrier H) : grp_coset_rel x x.
Proof.
  apply grp_coset_of_equiv.
  reflexivity.
Qed.

Lemma grp_coset_sym (x y : carrier H) : grp_coset_rel x y → grp_coset_rel y x.
Proof.
  intro Hxy.
  unfold grp_coset_rel in *.
  apply (GrpImage_respects (grp_inv H (grp_mul H (grp_inv H y) x))).
  - rewrite grp_inv_mul.
    rewrite grp_inv_inv.
    reflexivity.
  - now apply GrpImage_inv.
Qed.

Lemma grp_coset_trans (x y z : carrier H) :
  grp_coset_rel x y → grp_coset_rel y z → grp_coset_rel x z.
Proof.
  intros Hxy Hyz.
  unfold grp_coset_rel in *.
  apply (GrpImage_respects
           (grp_mul H (grp_mul H (grp_inv H z) y)
                      (grp_mul H (grp_inv H y) x))).
  - rewrite grp_mul_assoc.
    rewrite <- (grp_mul_assoc H y (grp_inv H y) x).
    rewrite grp_mul_inv_r.
    now rewrite grp_mul_unit_l.
  - now apply GrpImage_mul.
Qed.

Lemma grp_coset_equivalence : Equivalence grp_coset_rel.
Proof.
  constructor.
  - exact grp_coset_refl.
  - exact grp_coset_sym.
  - exact grp_coset_trans.
Qed.

(* 相关说明。 （已译） *)
Definition Grp_Coset : SetoidObject :=
  {| carrier   := carrier H
   ; is_setoid := {| equiv        := grp_coset_rel
                   ; setoid_equiv := grp_coset_equivalence |} |}.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma GrpImage_coset (x y : carrier H) :
  grp_coset_rel x y → GrpImage f x → GrpImage f y.
Proof.
  intros Hxy Hx.
  apply (GrpImage_respects (grp_mul H x (grp_inv H (grp_mul H (grp_inv H y) x)))).
  - rewrite grp_inv_mul.
    rewrite grp_inv_inv.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_l.
  - apply GrpImage_mul; [assumption|].
    now apply GrpImage_inv.
Qed.

Lemma GrpImage_coset_iff (x y : carrier H) :
  grp_coset_rel x y → GrpImage f x ↔ GrpImage f y.
Proof.
  intro Hxy.
  split.
  - now apply GrpImage_coset.
  - apply GrpImage_coset.
    now apply grp_coset_sym.
Qed.

(* Left translation [a], setoid map coset space: coset
 关系 preserved because (ay)⁻¹(ax) ≈ y⁻¹x. （已译） *)
Program Definition grp_translate (a : carrier H) :
  SetoidMorphism Grp_Coset Grp_Coset := {| morphism := grp_mul H a |}.
Next Obligation.
  intros a x y Hxy.
  simpl in *.
  unfold grp_coset_rel in *.
  apply (GrpImage_respects (grp_mul H (grp_inv H y) x)); [|assumption].
  rewrite grp_inv_mul.
  rewrite grp_mul_assoc.
  rewrite <- (grp_mul_assoc H (grp_inv H a) a x).
  rewrite grp_mul_inv_l.
  now rewrite grp_mul_unit_l.
Qed.

(* 相关说明。 （已译） *)
Lemma GrpImage_translate (m c : carrier H) :
  GrpImage f m →
  (GrpImage f (grp_mul H (grp_inv H m) c) ↔ GrpImage f c).
Proof.
  intro Hm.
  split.
  - intro Hmc.
    apply (GrpImage_respects (grp_mul H m (grp_mul H (grp_inv H m) c))).
    + rewrite <- grp_mul_assoc.
      rewrite grp_mul_inv_r.
      apply grp_mul_unit_l.
    + now apply GrpImage_mul.
  - intro Hc.
    apply GrpImage_mul; [|assumption].
    now apply GrpImage_inv.
Qed.

End Image.

Arguments grp_coset_rel {G H} f _ _.
Arguments Grp_Coset {G H} f.
Arguments grp_translate {G H} f a.

(* 相关说明。 （已译） *)

(* A permutation of a setoid: an invertible setoid map, presented as a pair of
   setoid maps with both round trips up to `≈`.  Nothing here is a bijection on
   the nose; the inverse is data, so no choice principle is involved. *)
Record SetoidPermutation (X : SetoidObject) := {
  sperm_to   : SetoidMorphism X X;
  sperm_from : SetoidMorphism X X;

  sperm_to_from : ∀ x, sperm_to (sperm_from x) ≈ x;
  sperm_from_to : ∀ x, sperm_from (sperm_to x) ≈ x
}.

Arguments sperm_to {X} _.
Arguments sperm_from {X} _.
Arguments sperm_to_from {X} _ _.
Arguments sperm_from_to {X} _ _.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sperm_from_determined {X : SetoidObject} (p q : SetoidPermutation X) :
  (∀ x, sperm_to p x ≈ sperm_to q x) → ∀ x, sperm_from p x ≈ sperm_from q x.
Proof.
  intros Hpq x.
  transitivity (sperm_from q (sperm_to q (sperm_from p x))).
  - symmetry.
    apply (sperm_from_to q).
  - apply (proper_morphism (sperm_from q)).
    transitivity (sperm_to p (sperm_from p x)).
    + symmetry.
      apply Hpq.
    + apply (sperm_to_from p).
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance SetoidPermutation_Setoid (X : SetoidObject) :
  Setoid (SetoidPermutation X) := {|
  equiv := λ p q, ∀ x, sperm_to p x ≈ sperm_to q x
|}.
Next Obligation.
  intro X.
  constructor.
  - intros p x.
    reflexivity.
  - intros p q Hpq x.
    now symmetry.
  - intros p q r Hpq Hqr x.
    now transitivity (sperm_to q x).
Qed.

(* 相关说明。 （已译） *)
Definition SetoidPermutation_PropEquiv (X : SetoidObject)
  (PX : PropEquiv (is_setoid X)) : PropEquiv (SetoidPermutation_Setoid X).
Proof.
  unshelve refine
    {| pequiv := fun p q : SetoidPermutation X =>
                   forall x : carrier X,
                     @pequiv _ _ PX (sperm_to p x) (sperm_to q x) |}.
  - intros p q Hpq x; exact (pequiv_to _ _ (Hpq x)).
  - intros p q Hpq x; exact (pequiv_from _ _ (Hpq x)).
Defined.

Program Definition sperm_id (X : SetoidObject) : SetoidPermutation X := {|
  sperm_to   := setoid_morphism_id;
  sperm_from := setoid_morphism_id
|}.
Next Obligation. intros X x; reflexivity. Qed.
Next Obligation. intros X x; reflexivity. Qed.

Program Definition sperm_compose {X : SetoidObject}
        (p q : SetoidPermutation X) : SetoidPermutation X := {|
  sperm_to   := setoid_morphism_compose (sperm_to p) (sperm_to q);
  sperm_from := setoid_morphism_compose (sperm_from q) (sperm_from p)
|}.
Next Obligation.
  intros X p q x; simpl.
  rewrite (sperm_to_from q (sperm_from p x)).
  apply (sperm_to_from p).
Qed.
Next Obligation.
  intros X p q x; simpl.
  rewrite (sperm_from_to p (sperm_to q x)).
  apply (sperm_from_to q).
Qed.

Definition sperm_inv {X : SetoidObject} (p : SetoidPermutation X) :
  SetoidPermutation X := {|
  sperm_to      := sperm_from p;
  sperm_from    := sperm_to p;
  sperm_to_from := sperm_from_to p;
  sperm_from_to := sperm_to_from p
|}.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SymGrp (X : SetoidObject) (PX : PropEquiv (is_setoid X)) :
  GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier   := SetoidPermutation X
                   ; is_setoid := SetoidPermutation_Setoid X |};
    grp_unit := sperm_id X;
    grp_mul  := @sperm_compose X;
    grp_inv  := @sperm_inv X;
    grp_prop := SetoidPermutation_PropEquiv X PX
  |}.
  - (* composition respects `≈` *)
    intros p p' Hp q q' Hq x; simpl.
    rewrite (Hq x).
    exact (Hp (sperm_to q' x)).
  - (* associativity, on the nose after unfolding composition *)
    intros p q r x; simpl.
    reflexivity.
  - (* left unit *)
    intros p x; simpl.
    reflexivity.
  - (* left inverse: the backward round trip *)
    intros p x; simpl.
    apply (sperm_from_to p).
Defined.

(** ** Inner automorphisms *)

Program Definition grp_conj_map (K : GrpObject) (s : carrier K) :
  SetoidMorphism (grp_setoid K) (grp_setoid K) :=
  {| morphism := λ a, grp_mul K (grp_mul K s a) (grp_inv K s) |}.
Next Obligation.
  intros K s a b Hab.
  now rewrite Hab.
Qed.

Lemma grp_conj_mul (K : GrpObject) (s a b : carrier K) :
  grp_mul K (grp_mul K s (grp_mul K a b)) (grp_inv K s)
    ≈ grp_mul K (grp_mul K (grp_mul K s a) (grp_inv K s))
                (grp_mul K (grp_mul K s b) (grp_inv K s)).
Proof.
  assert (Hcancel : ∀ c : carrier K,
             grp_mul K (grp_inv K s) (grp_mul K s c) ≈ c).
  { intro c.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l. }
  rewrite !grp_mul_assoc.
  rewrite Hcancel.
  reflexivity.
Qed.

(* Conjugation by a fixed element is an endomorphism of the group; classically
   it is the inner automorphism at [s], but invertibility is neither proved
   here nor needed -- only the homomorphism property is used below. *)
Definition grp_conj (K : GrpObject) (s : carrier K) : K ~{Grp}~> K :=
  Build_GrpHom' (grp_conj_map K s) (grp_conj_mul K s).

(* 相关说明。 （已译） *)

Section Epi.

Context {G H : GrpObject}.
Context (f : G ~{Grp}~> H).

(* The stable-valued "power set" coset space: setoid maps the
 cosets image stable propositions. This H-set the
 论元 permutes. （已译） *)
Definition GrpCosetPower : SetoidObject :=
  {| carrier   := SetoidMorphism (Grp_Coset f) StableSetoid
   ; is_setoid := @SetoidMorphism_Setoid (Grp_Coset f) StableSetoid |}.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_coset_power_prop : PropEquiv (is_setoid GrpCosetPower) :=
  @hom_PropEquiv (Grp_Coset f) StableSetoid StableSetoid_PropEquiv.

(* The left action of H, (h · S)(c) = S(h⁻¹ c). *)
Program Definition grp_act_map (h : carrier H) :
  SetoidMorphism GrpCosetPower GrpCosetPower :=
  {| morphism := λ S,
       setoid_morphism_compose S (grp_translate f (grp_inv H h)) |}.
Next Obligation.
  intros h S S' HS c; simpl.
  exact (HS _).
Qed.

Program Definition grp_act (h : carrier H) :
  SetoidPermutation GrpCosetPower := {|
  sperm_to   := grp_act_map h;
  sperm_from := grp_act_map (grp_inv H h)
|}.
Next Obligation.
  intros h S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  rewrite grp_inv_inv.
  rewrite <- grp_mul_assoc.
  rewrite grp_mul_inv_r.
  apply grp_mul_unit_l.
Qed.
Next Obligation.
  intros h S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  rewrite grp_inv_inv.
  rewrite <- grp_mul_assoc.
  rewrite grp_mul_inv_l.
  apply grp_mul_unit_l.
Qed.

Program Definition grp_action_map :
  SetoidMorphism (grp_setoid H) (grp_setoid (SymGrp GrpCosetPower grp_coset_power_prop)) :=
  {| morphism := grp_act |}.
Next Obligation.
  intros h h' Hh S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  now rewrite Hh.
Qed.

Lemma grp_action_mul (h1 h2 : carrier H) :
  grp_act (grp_mul H h1 h2)
    ≈ grp_mul (SymGrp GrpCosetPower grp_coset_power_prop) (grp_act h1) (grp_act h2).
Proof.
  intros S c; simpl.
  apply (proper_morphism S).
  apply grp_coset_of_equiv.
  rewrite grp_inv_mul.
  apply grp_mul_assoc.
Qed.

(* H acts on the stable power set of its coset space by permutations. *)
Definition grp_action : H ~{Grp}~> SymGrp GrpCosetPower grp_coset_power_prop :=
  Build_GrpHom' grp_action_map grp_action_mul.

(* 相关说明。 （已译） *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_twist_ty (S : carrier GrpCosetPower) (c : carrier H) : Prop :=
  (GrpImage f c → ¬ `1 (S c)) /\ (¬ GrpImage f c → `1 (S c)).

Lemma grp_twist_stable (S : carrier GrpCosetPower) (c : carrier H) :
  Stable (grp_twist_ty S c).
Proof.
  unfold grp_twist_ty.
  apply stable_and.
  - apply stable_arrow.
    apply stable_not.
  - apply stable_arrow.
    exact (`2 (S c)).
Qed.

Program Definition grp_twist_val (S : carrier GrpCosetPower) :
  SetoidMorphism (Grp_Coset f) StableSetoid :=
  {| morphism := λ c, (grp_twist_ty S c; grp_twist_stable S c) |}.
Next Obligation.
  intros S x y Hxy.
  destruct (GrpImage_coset_iff f x y Hxy) as [Exy Eyx].
  destruct (proper_morphism S x y Hxy) as [Sxy Syx].
  split.
  - intros [A B].
    split.
    + intros hy sy.
      exact (A (Eyx hy) (Syx sy)).
    + intro ny.
      apply Sxy, B.
      intro hx.
      exact (ny (Exy hx)).
  - intros [A B].
    split.
    + intros hx sx.
      exact (A (Exy hx) (Sxy sx)).
    + intro nx.
      apply Syx, B.
      intro hy.
      exact (nx (Eyx hy)).
Qed.

Program Definition grp_twist_map :
  SetoidMorphism GrpCosetPower GrpCosetPower :=
  {| morphism := grp_twist_val |}.
Next Obligation.
  intros S S' HS c.
  destruct (HS c) as [Scc' Sc'c].
  split.
  - intros [A B].
    split.
    + intros hc sc'.
      exact (A hc (Sc'c sc')).
    + intro nc.
      exact (Scc' (B nc)).
  - intros [A B].
    split.
    + intros hc sc.
      exact (A hc (Scc' sc)).
    + intro nc.
      exact (Sc'c (B nc)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_twist_involutive (S : carrier GrpCosetPower) (c : carrier H) :
  grp_twist_ty (grp_twist_val S) c ↔ `1 (S c).
Proof.
  split.
  - intro A.
    apply (`2 (S c)).
    intro ns.
    assert (nne : ¬¬ GrpImage f c).
    { intro ne.
      exact (ns (proj2 (proj2 A ne) ne)). }
    assert (Ht : grp_twist_ty S c).
    { split.
      - intros _.
        exact ns.
      - intro ne.
        destruct (nne ne). }
    exact (nne (λ He, proj1 A He Ht)).
  - intros Hs.
    split.
    + intros He Ht.
      exact (proj1 Ht He Hs).
    + intro Hne.
      split.
      * intro He.
        destruct (Hne He).
      * intros _.
        exact Hs.
Qed.

Lemma grp_twist_roundtrip (S : carrier GrpCosetPower) :
  grp_twist_map (grp_twist_map S) ≈ S.
Proof.
  intro c.
  apply grp_twist_involutive.
Qed.

Definition grp_twist : carrier (SymGrp GrpCosetPower grp_coset_power_prop) := {|
  sperm_to      := grp_twist_map;
  sperm_from    := grp_twist_map;
  sperm_to_from := grp_twist_roundtrip;
  sperm_from_to := grp_twist_roundtrip
|}.

(* 相关说明。 （已译） *)
Definition grp_twisted_action : H ~{Grp}~> SymGrp GrpCosetPower grp_coset_power_prop :=
  grp_conj (SymGrp GrpCosetPower grp_coset_power_prop) grp_twist ∘[Grp] grp_action.

(* 相关说明。 （已译） *)

Lemma grp_twist_act_commute (g : carrier G) (S : carrier GrpCosetPower) :
  grp_twist_map (grp_act_map (grp_map f g) S)
    ≈ grp_act_map (grp_map f g) (grp_twist_map S).
Proof.
  intro c.
  assert (Hm : GrpImage f (grp_map f g)).
  { exists g.
    reflexivity. }
  destruct (GrpImage_translate f (grp_map f g) c Hm) as [Emc Ecm].
  split.
  - intros [A B].
    split.
    + intros hmc smc.
      exact (A (Emc hmc) smc).
    + intro nmc.
      apply B.
      intro hc.
      exact (nmc (Ecm hc)).
  - intros [A B].
    split.
    + intros hc smc.
      exact (A (Ecm hc) smc).
    + intro nc.
      apply B.
      intro hmc.
      exact (nc (Emc hmc)).
Qed.

(* The two homomorphisms agree after f. *)
Lemma grp_twisted_action_agrees :
  grp_twisted_action ∘[Grp] f ≈ grp_action ∘[Grp] f.
Proof.
  intro g.
  intro S.
  transitivity (grp_act_map (grp_map f g)
                  (grp_twist_map (grp_twist_map S))).
  - apply grp_twist_act_commute.
  - apply (proper_morphism (grp_act_map (grp_map f g))).
    apply grp_twist_roundtrip.
Qed.

(* 相关说明。 （已译） *)
Program Definition grp_dense_subset :
  SetoidMorphism (Grp_Coset f) StableSetoid :=
  {| morphism := λ c, (¬¬ GrpImage f c ; stable_not_not (GrpImage f c)) |}.
Next Obligation.
  intros x y Hxy.
  destruct (GrpImage_coset_iff f x y Hxy) as [Exy Eyx].
  split.
  - intros nnx ny.
    exact (nnx (λ hx, ny (Exy hx))).
  - intros nny nx.
    exact (nny (λ hy, nx (Eyx hy))).
Qed.

(* 相关说明。 （已译） *)
Lemma grp_image_misses_translate (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  ¬ GrpImage f (grp_mul H (grp_inv H h0) (grp_unit H)).
Proof.
  intro Hin.
  apply Hh0.
  apply (GrpImage_respects f
           (grp_inv H (grp_mul H (grp_inv H h0) (grp_unit H)))).
  - rewrite grp_mul_unit_r.
    apply grp_inv_inv.
  - now apply GrpImage_inv.
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_action_not_identity (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  grp_act h0 ≈ grp_unit (SymGrp GrpCosetPower grp_coset_power_prop) → False.
Proof.
  intro Heq.
  destruct (Heq grp_dense_subset (grp_unit H)) as [Hfwd Hbwd].
  assert (Hnn : ¬¬ GrpImage f (grp_unit H)).
  { intro Hno.
    exact (Hno (GrpImage_unit f)). }
  exact (Hbwd Hnn (grp_image_misses_translate h0 Hh0)).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition grp_coset_indicator (x0 : carrier H) :
  SetoidMorphism (Grp_Coset f) StableSetoid :=
  {| morphism := λ c, (¬¬ grp_coset_rel f c x0 ; stable_not_not _) |}.
Next Obligation.
  intros x0 x y Hxy.
  split.
  - intros nnx ny.
    apply nnx; intro hx.
    exact (ny (grp_coset_trans f y x x0 (grp_coset_sym f x y Hxy) hx)).
  - intros nny nx.
    apply nny; intro hy.
    exact (nx (grp_coset_trans f x y x0 Hxy hy)).
Qed.

(* 相关说明。 （已译） *)
Lemma grp_coset_indicator_base :
  grp_coset_indicator (grp_unit H) ≈ grp_dense_subset.
Proof.
  intro c.
  assert (Hto : @equiv _ (is_setoid (grp_setoid H))
                  (grp_mul H (grp_inv H (grp_unit H)) c) c).
  { rewrite grp_inv_unit.
    apply grp_mul_unit_l. }
  assert (Hfrom : @equiv _ (is_setoid (grp_setoid H)) c
                    (grp_mul H (grp_inv H (grp_unit H)) c)).
  { symmetry.
    exact Hto. }
  split.
  - intros nn nc.
    apply nn; intro hc.
    exact (nc (GrpImage_respects f _ c Hto hc)).
  - intros nn nc.
    apply nn; intro hc.
    exact (nc (GrpImage_respects f c _ Hfrom hc)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_act_moves_coset (m x0 : carrier H) :
  ¬ GrpImage f (grp_mul H (grp_inv H x0) (grp_mul H (grp_inv H m) x0)) →
  grp_act_map m (grp_coset_indicator x0) ≈ grp_coset_indicator x0 → False.
Proof.
  intros Hout Heq.
  destruct (Heq x0) as [_ Hbwd].
  exact (Hbwd (λ n, n (grp_coset_refl f x0)) Hout).
Qed.

(* The same thing one level up, stated element OF image: if
 some conjugate f g escapes image, then f g does not act the
 恒等 permutation [GrpCosetPower]. （已译） *)
Lemma grp_image_acts_nontrivially (g : carrier G) (x0 : carrier H) :
  ¬ GrpImage f (grp_mul H (grp_inv H x0)
                  (grp_mul H (grp_inv H (grp_map f g)) x0)) →
  grp_act (grp_map f g) ≈ grp_unit (SymGrp GrpCosetPower grp_coset_power_prop) → False.
Proof.
  intros Hout Heq.
  exact (grp_act_moves_coset (grp_map f g) x0 Hout
           (Heq (grp_coset_indicator x0))).
Qed.

(* 相关说明。 （已译） *)
Lemma grp_twist_act_not_commute (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  grp_twist_map (grp_act_map h0 grp_dense_subset)
    ≈ grp_act_map h0 (grp_twist_map grp_dense_subset) → False.
Proof.
  intro Heq.
  pose proof (grp_image_misses_translate h0 Hh0) as Hne.
  destruct (Heq (grp_unit H)) as [Hfwd Hbwd].
  assert (HL : grp_twist_ty (grp_act_map h0 grp_dense_subset) (grp_unit H)).
  { split.
    - intros _ Hnn.
      exact (Hnn Hne).
    - intro Hno.
      destruct (Hno (GrpImage_unit f)). }
  destruct (Hfwd HL) as [_ B].
  exact (B Hne Hne).
Qed.

(* The two homomorphisms distinct hom-setoid [Grp], witnessed at
 concrete element [h0] H concrete permutation 论元
 [grp_twist_map grp_dense_subset]. （已译） *)
Lemma grp_actions_differ (h0 : carrier H) (Hh0 : ¬ GrpImage f h0) :
  grp_twisted_action ≈ grp_action → False.
Proof.
  intro Heq.
  apply (grp_twist_act_not_commute h0 Hh0).
  transitivity (grp_twist_map
                  (grp_act_map h0 (grp_twist_map
                                     (grp_twist_map grp_dense_subset)))).
  - apply (proper_morphism grp_twist_map).
    apply (proper_morphism (grp_act_map h0)).
    symmetry.
    apply grp_twist_roundtrip.
  - exact (Heq h0 (grp_twist_map grp_dense_subset)).
Qed.

(* The twist never 恒等 permutation, any f whatsoever: the
 permutation group play therefore never trivial group, the
 witness above not secretly unit. （已译） *)
Lemma grp_twist_not_identity :
  grp_twist ≈ grp_unit (SymGrp GrpCosetPower grp_coset_power_prop) → False.
Proof.
  intro Heq.
  destruct (Heq grp_dense_subset (grp_unit H)) as [Hfwd Hbwd].
  assert (Hnn : ¬¬ GrpImage f (grp_unit H)).
  { intro Hno.
    exact (Hno (GrpImage_unit f)). }
  destruct (Hbwd Hnn) as [A _].
  exact (A (GrpImage_unit f) Hnn).
Qed.

(** ** The theorems *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem grp_not_epic_of_witness (h0 : carrier H) :
  ¬ GrpImage f h0 → ¬ Epic f.
Proof.
  intros Hh0 [Hepic].
  apply (grp_actions_differ h0 Hh0).
  apply Hepic.
  apply grp_twisted_action_agrees.
Qed.

(* 相关说明。 （已译） *)
Theorem grp_epic_image_dense :
  Epic f → ∀ h : carrier H, ¬¬ GrpImage f h.
Proof.
  intros Hepic h Hno.
  exact (grp_not_epic_of_witness h Hno Hepic).
Qed.

(* The easy direction, unconditional. *)
Theorem grp_surjective_is_epic : GrpSurjective f → Epic f.
Proof.
  intro Hsurj.
  constructor.
  intros z g1 g2 Heq h.
  destruct (Hsurj h) as [g Hg].
  rewrite <- Hg.
  exact (Heq g).
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GrpImageStable : Type := ∀ h : carrier H, Stable (GrpImage f h).

(* A decision procedure for image membership is one way to have it. *)
Definition GrpImageDecidable : Type :=
  ∀ h : carrier H, GrpImage f h ∨ ¬ GrpImage f h.

Lemma GrpImageDecidable_Stable : GrpImageDecidable → GrpImageStable.
Proof.
  intros Hdec h Hnn.
  destruct (Hdec h) as [Hin|Hout].
  - exact Hin.
  - destruct (Hnn Hout).
Qed.

Theorem grp_epic_is_surjective : GrpImageStable → Epic f → GrpSurjective f.
Proof.
  intros Hstable Hepic h.
  apply Hstable.
  exact (grp_epic_image_dense Hepic h).
Qed.

(* 相关说明。 （已译） *)
Theorem grp_epic_iff_surjective :
  GrpImageStable → (Epic f ↔ GrpSurjective f).
Proof.
  intro Hstable.
  split.
  - now apply grp_epic_is_surjective.
  - apply grp_surjective_is_epic.
Qed.

(* * ** The 假设 conclusion （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The trivial half: surjectivity gives stability outright. *)
Theorem surjective_gives_stable : GrpSurjective f → GrpImageStable.
Proof. intros Hs h _; exact (Hs h). Qed.

(* Hence EPIMORPHISM 假设 EQUIVALENT conclusion it
 supposed buy, [grp_epic_is_surjective] adds nothing beyond the
 unconditional [grp_epic_image_dense]. （已译） *)
Theorem stability_is_the_conclusion (Hepic : Epic f) :
  GrpImageStable ↔ GrpSurjective f.
Proof.
  split.
  - intro Hst.
    exact (grp_epic_is_surjective Hst Hepic).
  - exact surjective_gives_stable.
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition DenseImpliesSurjective : Type :=
  (∀ h : carrier H, ¬¬ GrpImage f h) → GrpSurjective f.

Theorem weaker_hypothesis_suffices :
  DenseImpliesSurjective → Epic f → GrpSurjective f.
Proof.
  intros Hw He.
  exact (Hw (grp_epic_image_dense He)).
Qed.

Theorem stable_implies_weaker : GrpImageStable → DenseImpliesSurjective.
Proof. intros Hst Hd h; exact (Hst h (Hd h)). Qed.

Theorem surjective_gives_weaker : GrpSurjective f → DenseImpliesSurjective.
Proof. intros Hs _; exact Hs. Qed.

(* 相关说明。 （已译） *)
Theorem weaker_is_the_conclusion (Hepic : Epic f) :
  DenseImpliesSurjective ↔ GrpSurjective f.
Proof.
  split.
  - intro Hw.
    exact (weaker_hypothesis_suffices Hw Hepic).
  - exact surjective_gives_weaker.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CosetPlusPt : Type := carrier (Grp_Coset f) ∨ poly_unit.

Definition cpp_rel : crelation CosetPlusPt := λ x y,
  match x, y with
  | inl c, inl d => grp_coset_rel f c d
  | inr _, inr _ => poly_unit
  | _, _         => False
  end.

Lemma cpp_equivalence : Equivalence cpp_rel.
Proof.
  constructor.
  - intros [c|u]; simpl; [ apply grp_coset_refl | exact ttt ].
  - intros [c|u] [d|v]; simpl; try contradiction;
      [ apply grp_coset_sym | intros _; exact ttt ].
  - intros [c|u] [d|v] [e|w]; simpl; try contradiction;
      [ apply grp_coset_trans | intros _ _; exact ttt ].
Qed.

Definition CosetPlusPtSetoid : SetoidObject :=
  {| carrier   := CosetPlusPt
   ; is_setoid := {| equiv := cpp_rel ; setoid_equiv := cpp_equivalence |} |}.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cpp_is_pt_or_not (x : CosetPlusPt) :
  (@equiv _ (is_setoid CosetPlusPtSetoid) x (inr ttt))
    ∨ ¬ (@equiv _ (is_setoid CosetPlusPtSetoid) x (inr ttt)).
Proof.
  destruct x as [c|u].
  - right; intro Hx; exact Hx.
  - left; exact ttt.
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem transposition_decides_image
  (t : SetoidPermutation CosetPlusPtSetoid)
  (Hbase : ∀ c, GrpImage f c →
             @equiv _ (is_setoid CosetPlusPtSetoid)
               (sperm_to t (inl c)) (inr ttt)) :
  GrpImageDecidable.
Proof.
  intro h.
  destruct (cpp_is_pt_or_not (sperm_to t (inl h))) as [Hpt|Hnpt].
  - left.
    assert (Hsame : @equiv _ (is_setoid CosetPlusPtSetoid)
                      (sperm_to t (inl h)) (sperm_to t (inl (grp_unit H)))).
    { transitivity (inr ttt : CosetPlusPt).
      - exact Hpt.
      - symmetry.
        exact (Hbase (grp_unit H) (GrpImage_unit f)). }
    assert (Hback : @equiv _ (is_setoid CosetPlusPtSetoid)
                      (inl h) (inl (grp_unit H))).
    { transitivity (sperm_from t (sperm_to t (inl h))).
      - symmetry; apply (sperm_from_to t).
      - transitivity (sperm_from t (sperm_to t (inl (grp_unit H)))).
        + apply (proper_morphism (sperm_from t)); exact Hsame.
        + apply (sperm_from_to t). }
    simpl in Hback.
    unfold grp_coset_rel in Hback.
    apply (GrpImage_respects f (grp_mul H (grp_inv H (grp_unit H)) h)).
    + rewrite grp_inv_unit.
      apply grp_mul_unit_l.
    + exact Hback.
  - right.
    intro Hin.
    exact (Hnpt (Hbase h Hin)).
Qed.

End Epi.

(* ------------------------------------------------------------------------ *)
(** ** Concrete witnesses *)

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition grp_two_carrier : Type := poly_unit ∨ poly_unit.

Definition grp_two_zero : grp_two_carrier := inl ttt.
Definition grp_two_one  : grp_two_carrier := inr ttt.

Definition grp_two_rel : crelation grp_two_carrier := λ x y,
  match x, y with
  | inl _, inl _ => poly_unit
  | inr _, inr _ => poly_unit
  | _, _ => False
  end.

Lemma grp_two_equivalence : Equivalence grp_two_rel.
Proof.
  constructor.
  - intros [u|u]; exact ttt.
  - intros [u|u] [v|v] Hxy; try exact ttt; contradiction.
  - intros [u|u] [v|v] [w|w] Hxy Hyz; try exact ttt; contradiction.
Qed.

Definition grp_two_add (x y : grp_two_carrier) : grp_two_carrier :=
  match x, y with
  | inl _, _      => y
  | _, inl _      => x
  | inr _, inr _  => grp_two_zero
  end.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_two_prel (x y : grp_two_carrier) : Prop :=
  match x, y with
  | inl _, inl _ => True
  | inr _, inr _ => True
  | _, _ => False
  end.

Definition grp_two_setoid : SetoidObject :=
  {| carrier   := grp_two_carrier
   ; is_setoid := {| equiv        := grp_two_rel
                   ; setoid_equiv := grp_two_equivalence |} |}.

Definition grp_two_prop : PropEquiv (is_setoid grp_two_setoid).
Proof.
  unshelve refine {| pequiv := grp_two_prel |}.
  - intros [u|u] [v|v] h; simpl in *; try exact ttt; contradiction.
  - intros [u|u] [v|v] h; simpl in *; try exact I; contradiction.
Defined.

(* Z/2 again, on a universe-polymorphic carrier: addition modulo two, with
   every element its own inverse. *)
Definition GrpTwo : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := grp_two_setoid;
    grp_unit := grp_two_zero;
    grp_mul  := grp_two_add;
    grp_inv  := λ x, x;
    grp_prop := grp_two_prop
  |}.
  - intros x x' Hx y y' Hy.
    destruct x as [|], x' as [|], y as [|], y' as [|];
      simpl in *; try contradiction; exact ttt.
  - intros a b c.
    destruct a as [|], b as [|], c as [|]; exact ttt.
  - intros a.
    destruct a as [|]; exact ttt.
  - intros a.
    destruct a as [|]; exact ttt.
Defined.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_two_incl : GrpTwo ~{Grp}~> Grp_product GrpTwo GrpTwo.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom GrpTwo (Grp_product GrpTwo GrpTwo)
       {| morphism := λ x, (x, grp_two_zero) |} _ _).
  - intros x y Hxy.
    split; [exact Hxy | exact ttt].
  - split; exact ttt.
  - intros a b.
    split; [reflexivity | exact ttt].
Defined.

(* The image is a NON-TRIVIAL subgroup: (1,0) is in it ... *)
Example grp_two_incl_image_nontrivial :
  GrpImage grp_two_incl (grp_two_one, grp_two_zero).
Proof.
  exists grp_two_one.
  split; exact ttt.
Qed.

(* 相关说明。 （已译） *)
Example grp_two_incl_image_witness_not_unit :
  @equiv _ (grp_setoid (Grp_product GrpTwo GrpTwo))
    (grp_two_one, grp_two_zero) (grp_unit (Grp_product GrpTwo GrpTwo)) → False.
Proof.
  intros [H1 _].
  exact H1.
Qed.

(* ... and it is a PROPER subgroup: (0,1) has no preimage. *)
Lemma grp_two_incl_misses :
  ¬ GrpImage grp_two_incl (grp_two_zero, grp_two_one).
Proof.
  intros [b Hb].
  destruct Hb as [_ H2].
  exact H2.
Qed.

(* The two homomorphisms 进入 permutation group distinct IN THE
 HOM-SETOID [Grp], at concrete element (0,1) codomain. （已译） *)
Theorem grp_two_actions_differ :
  grp_twisted_action grp_two_incl ≈ grp_action grp_two_incl → False.
Proof.
  exact (grp_actions_differ grp_two_incl
           (grp_two_zero, grp_two_one) grp_two_incl_misses).
Qed.

(* Neither two permutations carry 论元 secretly the
 恒等: not twist, not action at missing element. （已译） *)
Theorem grp_two_action_not_identity :
  grp_act grp_two_incl (grp_two_zero, grp_two_one)
    ≈ grp_unit (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl)) → False.
Proof.
  exact (grp_action_not_identity grp_two_incl
           (grp_two_zero, grp_two_one) grp_two_incl_misses).
Qed.

(* The permutation group play not trivial group: twist a
 permutation different 恒等. （已译） *)
Theorem grp_two_twist_not_identity :
  grp_twist grp_two_incl
    ≈ grp_unit (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl)) → False.
Proof. exact (grp_twist_not_identity grp_two_incl). Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem grp_two_incl_image_acts_trivially :
  ∀ g : carrier GrpTwo,
    @equiv _ (grp_setoid (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl)))
      (grp_act grp_two_incl (grp_map grp_two_incl g))
      (grp_unit (SymGrp (GrpCosetPower grp_two_incl) (grp_coset_power_prop grp_two_incl))).
Proof.
  intros g S c; simpl.
  apply (proper_morphism S).
  exists g.
  destruct g as [u|u]; destruct c as [c1 c2];
    destruct c1 as [a|a]; destruct c2 as [b|b]; simpl; split; exact ttt.
Qed.

(* Hence [grp_two_incl] is not an epimorphism, by the main theorem. *)
Theorem grp_two_incl_not_epic : ¬ Epic grp_two_incl.
Proof.
  exact (grp_not_epic_of_witness grp_two_incl
           (grp_two_zero, grp_two_one) grp_two_incl_misses).
Qed.

(* The 假设 classical form, discharged concrete finite
 group: membership image [grp_two_incl] decidable, hence
 stable. （已译） *)
Definition grp_two_incl_decidable : GrpImageDecidable grp_two_incl.
Proof.
  intros [x y].
  destruct y as [u|u].
  - left.
    exists x.
    split; [reflexivity | exact ttt].
  - right.
    intros [b Hb].
    destruct Hb as [_ H2].
    exact H2.
Defined.

Definition grp_two_incl_epic_iff_surjective :
  Epic grp_two_incl ↔ GrpSurjective grp_two_incl :=
  grp_epic_iff_surjective grp_two_incl
    (GrpImageDecidable_Stable grp_two_incl grp_two_incl_decidable).

(* 相关说明。 （已译） *)
Theorem grp_two_incl_not_epic_classically : ¬ Epic grp_two_incl.
Proof.
  intro Hepic.
  apply grp_two_incl_misses.
  exact (fst grp_two_incl_epic_iff_surjective Hepic
           (grp_two_zero, grp_two_one)).
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sym3_letter : Type := poly_unit ∨ (poly_unit ∨ poly_unit).

Definition sym3_l0 : sym3_letter := inl ttt.
Definition sym3_l1 : sym3_letter := inr (inl ttt).
Definition sym3_l2 : sym3_letter := inr (inr ttt).

Definition sym3_rel : crelation sym3_letter := λ x y,
  match x, y with
  | inl _, inl _             => poly_unit
  | inr (inl _), inr (inl _) => poly_unit
  | inr (inr _), inr (inr _) => poly_unit
  | _, _                     => False
  end.

Lemma sym3_equivalence : Equivalence sym3_rel.
Proof.
  constructor.
  - intros [u|[u|u]]; exact ttt.
  - intros [u|[u|u]] [v|[v|v]] Hxy; try exact ttt; contradiction.
  - intros [u|[u|u]] [v|[v|v]] [w|[w|w]] Hxy Hyz; try exact ttt; contradiction.
Qed.

Definition Sym3Letters : SetoidObject :=
  {| carrier   := sym3_letter
   ; is_setoid := {| equiv        := sym3_rel
                   ; setoid_equiv := sym3_equivalence |} |}.

(* The [Prop] 镜像 [sym3_rel], model [grp_two_prel] above and
 same reason: [GrpSym3] below [GrpObject] [SymGrp] asks
 setoid [PropEquiv]. （已译） *)
Definition sym3_prel (x y : sym3_letter) : Prop :=
  match x, y with
  | inl _, inl _             => True
  | inr (inl _), inr (inl _) => True
  | inr (inr _), inr (inr _) => True
  | _, _                     => False
  end.

Definition sym3_letters_prop : PropEquiv (is_setoid Sym3Letters).
Proof.
  unshelve refine {| pequiv := sym3_prel |}.
  - intros [u|[u|u]] [v|[v|v]] h; simpl in *; try exact ttt; contradiction.
  - intros [u|[u|u]] [v|[v|v]] h; simpl in *; try exact I; contradiction.
Defined.

Definition sym3_map (p : sym3_letter → sym3_letter)
           (Hp : ∀ x y, sym3_rel x y → sym3_rel (p x) (p y)) :
  SetoidMorphism Sym3Letters Sym3Letters.
Proof.
  unshelve notypeclasses refine {| morphism := p |}.
  exact Hp.
Defined.

(* 相关说明。 （已译） *)
Definition sym3_perm (p : sym3_letter → sym3_letter)
           (Hp : ∀ x y, sym3_rel x y → sym3_rel (p x) (p y))
           (Hi : ∀ x, sym3_rel (p (p x)) x) : SetoidPermutation Sym3Letters.
Proof.
  unshelve notypeclasses refine
    {| sperm_to := sym3_map p Hp ; sperm_from := sym3_map p Hp |}.
  - exact Hi.
  - exact Hi.
Defined.

(* 相关说明。 （已译） *)
Definition sym3_swap12 (x : sym3_letter) : sym3_letter :=
  match x with
  | inl u       => inl u
  | inr (inl u) => inr (inr u)
  | inr (inr u) => inr (inl u)
  end.

Lemma sym3_swap12_respects :
  ∀ x y, sym3_rel x y → sym3_rel (sym3_swap12 x) (sym3_swap12 y).
Proof.
  intros [u|[u|u]] [v|[v|v]] Hxy; try exact ttt; contradiction.
Qed.

Lemma sym3_swap12_involutive : ∀ x, sym3_rel (sym3_swap12 (sym3_swap12 x)) x.
Proof. intros [u|[u|u]]; exact ttt. Qed.

Definition sym3_s : SetoidPermutation Sym3Letters :=
  sym3_perm sym3_swap12 sym3_swap12_respects sym3_swap12_involutive.

(* 相关说明。 （已译） *)
Definition sym3_swap01 (x : sym3_letter) : sym3_letter :=
  match x with
  | inl u       => inr (inl u)
  | inr (inl u) => inl u
  | inr (inr u) => inr (inr u)
  end.

Lemma sym3_swap01_respects :
  ∀ x y, sym3_rel x y → sym3_rel (sym3_swap01 x) (sym3_swap01 y).
Proof.
  intros [u|[u|u]] [v|[v|v]] Hxy; try exact ttt; contradiction.
Qed.

Lemma sym3_swap01_involutive : ∀ x, sym3_rel (sym3_swap01 (sym3_swap01 x)) x.
Proof. intros [u|[u|u]]; exact ttt. Qed.

Definition sym3_a : SetoidPermutation Sym3Letters :=
  sym3_perm sym3_swap01 sym3_swap01_respects sym3_swap01_involutive.

(* 相关说明。 （已译） *)
Example sym3_swaps_act :
  (sym3_rel (sym3_swap12 sym3_l0) sym3_l0
     ∧ sym3_rel (sym3_swap12 sym3_l1) sym3_l2
     ∧ sym3_rel (sym3_swap12 sym3_l2) sym3_l1)
  ∧ (sym3_rel (sym3_swap01 sym3_l0) sym3_l1
       ∧ sym3_rel (sym3_swap01 sym3_l1) sym3_l0
       ∧ sym3_rel (sym3_swap01 sym3_l2) sym3_l2).
Proof. repeat split; exact ttt. Qed.

Definition GrpSym3 : GrpObject := SymGrp Sym3Letters sym3_letters_prop.

(* Z/2 included subgroup generated transposition last two
 letters. The law any content transposition squares
 恒等. （已译） *)
Definition sym3_of_two (x : grp_two_carrier) : SetoidPermutation Sym3Letters :=
  match x with
  | inl _ => sperm_id Sym3Letters
  | inr _ => sym3_s
  end.

Definition grp_two_sym3 : GrpTwo ~{Grp}~> GrpSym3.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom GrpTwo GrpSym3 {| morphism := sym3_of_two |} _ _).
  - intros x y Hxy.
    destruct x as [u|u], y as [v|v]; simpl in Hxy;
      try contradiction; intros [z|[z|z]]; exact ttt.
  - intros [z|[z|z]]; exact ttt.
  - intros a b.
    destruct a as [u|u], b as [v|v]; intros [z|[z|z]]; exact ttt.
Defined.

(* It really 含入, so image really order two: a
 transposition not 恒等, witnessed at second letter. （已译） *)
Lemma grp_two_sym3_injective :
  ∀ a b : carrier GrpTwo,
    grp_map grp_two_sym3 a ≈ grp_map grp_two_sym3 b → a ≈ b.
Proof.
  intros [u|u] [v|v] Hab; try exact ttt; exact (Hab sym3_l1).
Qed.

(* 相关说明。 （已译） *)
Lemma grp_two_sym3_misses : ¬ GrpImage grp_two_sym3 sym3_a.
Proof.
  intros [g Hg].
  destruct g as [u|u]; exact (Hg sym3_l0).
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_two_sym3_conj_outside :
  ¬ GrpImage grp_two_sym3
      (grp_mul GrpSym3 (grp_inv GrpSym3 sym3_a)
         (grp_mul GrpSym3
            (grp_inv GrpSym3 (grp_map grp_two_sym3 grp_two_one)) sym3_a)).
Proof.
  intros [g Hg].
  destruct g as [u|u]; exact (Hg sym3_l0).
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem grp_two_sym3_moves_a_coset :
  grp_act_map grp_two_sym3 (grp_map grp_two_sym3 grp_two_one)
      (grp_coset_indicator grp_two_sym3 sym3_a)
    ≈ grp_coset_indicator grp_two_sym3 sym3_a → False.
Proof.
  exact (grp_act_moves_coset grp_two_sym3 _ sym3_a grp_two_sym3_conj_outside).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem grp_two_sym3_image_acts_nontrivially :
  grp_act grp_two_sym3 (grp_map grp_two_sym3 grp_two_one)
    ≈ grp_unit (SymGrp (GrpCosetPower grp_two_sym3) (grp_coset_power_prop grp_two_sym3)) → False.
Proof.
  exact (grp_image_acts_nontrivially grp_two_sym3 grp_two_one sym3_a
           grp_two_sym3_conj_outside).
Qed.

(* And main 定理 applies here too, so second witness witness
 论元 whole not degenerate step. （已译） *)
Theorem grp_two_sym3_not_epic : ¬ Epic grp_two_sym3.
Proof.
  exact (grp_not_epic_of_witness grp_two_sym3 sym3_a grp_two_sym3_misses).
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* The easy direction concrete surjection NOT 同构: the
 first projection Z/2 x Z/2 onto, hence epic, it not monic. （已译） *)
Definition grp_two_exl_surjective : GrpSurjective (@Grp_exl GrpTwo GrpTwo).
Proof.
  intro h.
  exists (h, grp_two_zero).
  reflexivity.
Defined.

Theorem grp_two_exl_epic : Epic (@Grp_exl GrpTwo GrpTwo).
Proof.
  exact (grp_surjective_is_epic (@Grp_exl GrpTwo GrpTwo)
           grp_two_exl_surjective).
Qed.

Lemma grp_two_exl_not_monic : Monic (@Grp_exl GrpTwo GrpTwo) → False.
Proof.
  intro Hm.
  destruct (Grp_injectivity_is_monic (@Grp_exl GrpTwo GrpTwo)) as [_ Hinj].
  assert (Heq : @equiv _ (grp_setoid (Grp_product GrpTwo GrpTwo))
                  (grp_two_zero, grp_two_zero) (grp_two_zero, grp_two_one)).
  { apply (Hinj Hm).
    reflexivity. }
  destruct Heq as [_ H2].
  exact H2.
Qed.

(* So [Epic] [Monic] do not coincide [Grp]: there epimorphism
 not monomorphism, hence not 同构. （已译） *)
Corollary grp_two_epic_not_monic :
  Epic (@Grp_exl GrpTwo GrpTwo) ∧ (Monic (@Grp_exl GrpTwo GrpTwo) → False).
Proof.
  split.
  - exact grp_two_exl_epic.
  - exact grp_two_exl_not_monic.
Qed.

(*
   本节说明 Epi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_two_incl_injective :
  ∀ a b : carrier GrpTwo,
    grp_map grp_two_incl a ≈ grp_map grp_two_incl b → a ≈ b.
Proof.
  intros a b Hab.
  exact (fst Hab).
Qed.

Theorem grp_two_incl_monic : Monic grp_two_incl.
Proof.
  exact (fst (Grp_injectivity_is_monic grp_two_incl) grp_two_incl_injective).
Qed.

Corollary grp_two_epic_monic_incomparable :
  (Epic (@Grp_exl GrpTwo GrpTwo) ∧ (Monic (@Grp_exl GrpTwo GrpTwo) → False))
    ∧ (Monic grp_two_incl ∧ ¬ Epic grp_two_incl).
Proof.
  split.
  - exact grp_two_epic_not_monic.
  - split.
    + exact grp_two_incl_monic.
    + exact grp_two_incl_not_epic.
Qed.
