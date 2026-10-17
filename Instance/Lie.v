Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Rng.Algebras.Associative.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 nLab:      https://ncatlab.org/nlab/show/Lie+algebra
 nLab:      https://ncatlab.org/nlab/show/universal+enveloping+algebra
 Wikipedia: https://en.wikipedia.org/wiki/Lie_algebra

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** * The category of Lie algebras *)

(** ** Objects

    A K-module together with a bracket.  Six laws, and the record is
    deliberately not minimal in one direction and deliberately minimal
    in another: additivity is carried in BOTH slots because the
    derivation of antisymmetry consumes both, while K-homogeneity is
    carried in the FIRST slot only, the second being the theorem
    [lie_br_smul_r] below. *)
Record LieObject (K : CRng) := {
  lie_mod : RModObject (`1 K);

  lie_br : carrier (cmon_setoid lie_mod) →
           carrier (cmon_setoid lie_mod) → carrier (cmon_setoid lie_mod);

  lie_br_respects : Proper (equiv ==> equiv ==> equiv) lie_br;

  (* Bilinearity: additive in each slot, homogeneous in the first. *)
  lie_br_add_l : ∀ x y z,
    lie_br (cmon_plus lie_mod x y) z
      ≈ cmon_plus lie_mod (lie_br x z) (lie_br y z);
  lie_br_add_r : ∀ x y z,
    lie_br x (cmon_plus lie_mod y z)
      ≈ cmon_plus lie_mod (lie_br x y) (lie_br x z);
  lie_br_smul_l : ∀ r x y,
    lie_br (rm_smul lie_mod r x) y ≈ rm_smul lie_mod r (lie_br x y);

  (* Alternating -- NOT antisymmetry; see the header. *)
  lie_alt : ∀ x, lie_br x x ≈ cmon_zero lie_mod;

  (* Jacobi, in the cyclic-sum-is-zero form. *)
  lie_jacobi : ∀ x y z,
    cmon_plus lie_mod (lie_br x (lie_br y z))
      (cmon_plus lie_mod (lie_br y (lie_br z x)) (lie_br z (lie_br x y)))
      ≈ cmon_zero lie_mod
}.

Arguments lie_mod {K} _.
Arguments lie_br {K} _ _ _.
Arguments lie_br_respects {K} _.
Arguments lie_br_add_l {K} _ _ _ _.
Arguments lie_br_add_r {K} _ _ _ _.
Arguments lie_br_smul_l {K} _ _ _ _.
Arguments lie_alt {K} _ _.
Arguments lie_jacobi {K} _ _ _ _.

#[export] Existing Instance lie_br_respects.

(** ** Alternating versus antisymmetric

    Stated for a BARE bracket on a module rather than for a
    [LieObject], so that the two candidate axioms are compared on equal
    terms and each passage shows in its own type exactly what it costs.
    [lie_alt_of_antisym] comes first precisely so that the additivity
    hypotheses are not yet in scope when it is proved: its statement is
    the evidence that it consumes none. *)

Definition TwoRegular {R : RingObject} (M : RModObject R) : Type :=
  ∀ m, cmon_plus M m m ≈ cmon_zero M → m ≈ cmon_zero M.

Section AlternatingVersusAntisymmetric.

Context {K : CRng}.
Context (M : RModObject (`1 K)).
Context (br : carrier (cmon_setoid M) →
              carrier (cmon_setoid M) → carrier (cmon_setoid M)).

(* Antisymmetry gives back alternating exactly when doubling is
   injective.  No additivity law is in scope here, and none is used. *)
Lemma lie_alt_of_antisym :
  TwoRegular M →
  (∀ x y, br x y ≈ ab_neg M (br y x)) →
  ∀ x, br x x ≈ cmon_zero M.
Proof.
  intros Hreg Hanti x.
  apply Hreg.
  rewrite (Hanti x x) at 2.
  apply (ab_neg_right M (br x x)).
Qed.

Context (br_respects : Proper (equiv ==> equiv ==> equiv) br).
Context (br_add_l : ∀ x y z,
  br (cmon_plus M x y) z ≈ cmon_plus M (br x z) (br y z)).
Context (br_add_r : ∀ x y z,
  br x (cmon_plus M y z) ≈ cmon_plus M (br x y) (br x z)).

#[local] Existing Instance br_respects.

(* Expanding [x+y, x+y] is where both additivity laws are spent. *)
Lemma lie_sum_zero_of_alt :
  (∀ x, br x x ≈ cmon_zero M) →
  ∀ x y, cmon_plus M (br x y) (br y x) ≈ cmon_zero M.
Proof using K M br br_respects br_add_l br_add_r.
  intros Halt x y.
  pose proof (Halt (cmon_plus M y x)) as H.
  rewrite (br_add_r (cmon_plus M y x) y x) in H.
  rewrite !(br_add_l y x) in H.
  rewrite (Halt y), (Halt x) in H.
  rewrite (cmon_plus_zero_l M) in H.
  rewrite (cmon_plus_zero_r M) in H.
  exact H.
Qed.

Lemma lie_antisym_of_alt :
  (∀ x, br x x ≈ cmon_zero M) →
  ∀ x y, br x y ≈ ab_neg M (br y x).
Proof using K M br br_respects br_add_l br_add_r.
  intros Halt x y.
  apply (ab_neg_unique M (br y x) (br x y)).
  apply lie_sum_zero_of_alt; assumption.
Qed.

End AlternatingVersusAntisymmetric.

(** ** Consequences of the axioms *)

Section LieDerived.

Context {K : CRng}.
Context (L : LieObject K).

Lemma lie_sum_zero (x y : carrier (cmon_setoid (lie_mod L))) :
  cmon_plus (lie_mod L) (lie_br L x y) (lie_br L y x)
    ≈ cmon_zero (lie_mod L).
Proof.
  apply (lie_sum_zero_of_alt (lie_mod L) (lie_br L) (lie_br_respects L)
           (lie_br_add_l L) (lie_br_add_r L) (lie_alt L)).
Qed.

(* ANTISYMMETRY IS A THEOREM, not a field. *)
Theorem lie_antisym (x y : carrier (cmon_setoid (lie_mod L))) :
  lie_br L x y ≈ ab_neg (lie_mod L) (lie_br L y x).
Proof.
  apply (lie_antisym_of_alt (lie_mod L) (lie_br L) (lie_br_respects L)
           (lie_br_add_l L) (lie_br_add_r L) (lie_alt L)).
Qed.

(* Homogeneity in the SECOND slot: antisymmetry twice, homogeneity in
   the first slot once, and [rm_smul_neg_r] to move the scalar past the
   negation. *)
Theorem lie_br_smul_r r (x y : carrier (cmon_setoid (lie_mod L))) :
  lie_br L x (rm_smul (lie_mod L) r y)
    ≈ rm_smul (lie_mod L) r (lie_br L x y).
Proof.
  rewrite (lie_antisym x (rm_smul (lie_mod L) r y)).
  rewrite (lie_br_smul_l L r y x).
  rewrite <- (rm_smul_neg_r (lie_mod L) r (lie_br L y x)).
  rewrite <- (lie_antisym x y).
  reflexivity.
Qed.

Lemma lie_br_zero_l (x : carrier (cmon_setoid (lie_mod L))) :
  lie_br L (cmon_zero (lie_mod L)) x ≈ cmon_zero (lie_mod L).
Proof.
  apply (ab_cancel_l (lie_mod L) (lie_br L (cmon_zero (lie_mod L)) x)).
  rewrite <- (lie_br_add_l L (cmon_zero (lie_mod L))
                (cmon_zero (lie_mod L)) x).
  rewrite (cmon_plus_zero_l (lie_mod L) (cmon_zero (lie_mod L))).
  symmetry; apply (cmon_plus_zero_r (lie_mod L)).
Qed.

Lemma lie_br_zero_r (x : carrier (cmon_setoid (lie_mod L))) :
  lie_br L x (cmon_zero (lie_mod L)) ≈ cmon_zero (lie_mod L).
Proof.
  rewrite (lie_antisym x (cmon_zero (lie_mod L))).
  rewrite (lie_br_zero_l x).
  apply (ab_neg_zero (lie_mod L)).
Qed.

End LieDerived.

(** ** Morphisms

    A module homomorphism preserving the bracket.  The hom-setoid is
    [RMod R]'s on the underlying module homomorphism, so the
    bracket-preservation proof is irrelevant, exactly as [AAlgHom]'s
    triangle proof is. *)
Record LieHom {K : CRng} (L M : LieObject K) := {
  lie_hom : RModHom (lie_mod L) (lie_mod M);

  lie_map_br : ∀ x y,
    cmon_map (rm_hom lie_hom) (lie_br L x y)
      ≈ lie_br M (cmon_map (rm_hom lie_hom) x)
                 (cmon_map (rm_hom lie_hom) y)
}.

Arguments lie_hom {K L M} _.
Arguments lie_map_br {K L M} _ _ _.

#[export]
Program Instance LieHom_Setoid {K : CRng} {L M : LieObject K} :
  Setoid (LieHom L M) := {|
  equiv := fun f g => lie_hom f ≈ lie_hom g
|}.
Next Obligation.
  intros K L M.
  constructor.
  - intros f; reflexivity.
  - intros f g Hfg; now symmetry.
  - intros f g h Hfg Hgh; now transitivity (lie_hom g).
Qed.

Program Definition lie_hom_id {K : CRng} {L : LieObject K} : LieHom L L := {|
  lie_hom := rmod_hom_id
|}.
Next Obligation. intros K L x y; simpl; reflexivity. Qed.

Program Definition lie_hom_compose {K : CRng} {L M N : LieObject K}
  (f : LieHom M N) (g : LieHom L M) : LieHom L N := {|
  lie_hom := rmod_hom_compose (lie_hom f) (lie_hom g)
|}.
Next Obligation.
  intros K L M N f g x y; simpl; unfold Basics.compose.
  rewrite (lie_map_br g x y).
  apply (lie_map_br f).
Qed.

Lemma lie_hom_compose_respects {K : CRng} {L M N : LieObject K} :
  Proper (equiv ==> equiv ==> equiv) (@lie_hom_compose K L M N).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(** ** The category *)

Program Definition Lie (K : CRng) : Category := {|
  obj     := LieObject K;
  hom     := @LieHom K;
  homset  := fun L M => @LieHom_Setoid K L M;
  id      := fun L => @lie_hom_id K L;
  compose := fun L M N f g => @lie_hom_compose K L M N f g;

  compose_respects := fun L M N => @lie_hom_compose_respects K L M N
|}.
Next Obligation. intros K L M f a; simpl; reflexivity. Qed.
Next Obligation. intros K L M f a; simpl; reflexivity. Qed.
Next Obligation. intros K L M N P f g h a; simpl; reflexivity. Qed.
Next Obligation. intros K L M N P f g h a; simpl; reflexivity. Qed.

(** ** The forgetful functors *)

Program Definition Lie_Forget_Mod (K : CRng) : Lie K ⟶ RMod (`1 K) := {|
  fobj := @lie_mod K;
  fmap := fun L M f => lie_hom f
|}.
Next Obligation. intros K L M f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K L a; simpl; reflexivity. Qed.
Next Obligation. intros K L M N f g a; simpl; reflexivity. Qed.

Program Definition Lie_Forget (K : CRng) : Lie K ⟶ Sets := {|
  fobj := fun L => cmon_setoid (lie_mod L);
  fmap := fun L M f => cmon_map (rm_hom (lie_hom f))
|}.
Next Obligation. intros K L M f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K L a; simpl; reflexivity. Qed.
Next Obligation. intros K L M N f g a; simpl; reflexivity. Qed.

(** ** The abelian Lie algebra on a module

    Every module carries the zero bracket, so [Lie K] is inhabited for
    every K with no witness-hunting.  This is the DEGENERATE case, and
    it is labelled as such: the non-degenerate witness is [Lie_UT2]. *)
Program Definition lie_abelian {K : CRng} (M : RModObject (`1 K))
  : LieObject K := {|
  lie_mod := M;
  lie_br  := fun _ _ => cmon_zero M
|}.
Next Obligation. intros K M x x' Hx y y' Hy; reflexivity. Qed.
Next Obligation.
  intros K M x y z; symmetry; apply (cmon_plus_zero_l M).
Qed.
Next Obligation.
  intros K M x y z; symmetry; apply (cmon_plus_zero_l M).
Qed.
Next Obligation.
  intros K M r x y; symmetry; apply (rm_smul_zero_r M r).
Qed.
Next Obligation. intros K M x; reflexivity. Qed.
Next Obligation.
  intros K M x y z.
  rewrite (cmon_plus_zero_l M (cmon_zero M)).
  apply (cmon_plus_zero_l M).
Qed.

Example lie_abelian_mod {K : CRng} (M : RModObject (`1 K)) :
  lie_mod (lie_abelian M) = M := eq_refl.

(** * Ring-level lemmas the commutator needs

    Four facts that mention no Lie algebra.  They are upstreaming
    candidates for Theory/Algebra/Rig.v and Instance/Rng.v; see the
    header for why they are declared here. *)

(* Ab/Subtract.v's shuffle, restated in ring vocabulary so that setoid
   rewriting -- which is keyed on the head symbol -- can use it beside
   [rig_distr_l] and [rig_distr_r].  The proof is a bare [exact]: the two
   statements are convertible, and nothing is reproved. *)
Lemma lie_sub_plus (R : RingObject) (a b c d : carrier (rig_setoid R)) :
  rig_add R (rig_add R a (ring_neg R b)) (rig_add R c (ring_neg R d))
    ≈ rig_add R (rig_add R a c) (ring_neg R (rig_add R b d)).
Proof. exact (ab_sub_plus (ring_ab R) a b c d). Qed.

Lemma lie_mul_neg_r (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R a (ring_neg R b) ≈ ring_neg R (rig_mul R a b).
Proof.
  assert (H : rig_add R (rig_mul R a (ring_neg R b)) (rig_mul R a b)
                ≈ rig_zero R).
  { rewrite <- rig_distr_l.
    rewrite (ring_neg_l R b).
    apply rig_mul_zero_r. }
  exact (ab_neg_unique (ring_ab R) (rig_mul R a b)
           (rig_mul R a (ring_neg R b)) H).
Qed.

Lemma lie_mul_neg_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  assert (H : rig_add R (rig_mul R (ring_neg R a) b) (rig_mul R a b)
                ≈ rig_zero R).
  { rewrite <- rig_distr_r.
    rewrite (ring_neg_l R a).
    apply rig_mul_zero_l. }
  exact (ab_neg_unique (ring_ab R) (rig_mul R a b)
           (rig_mul R (ring_neg R a) b) H).
Qed.

(* (a+b)+(c+d) ≈ (a+d)+(b+c) -- commutativity of addition, nothing else. *)
Lemma lie_add_shuffle4 (R : RigObject) (a b c d : carrier (rig_setoid R)) :
  rig_add R (rig_add R a b) (rig_add R c d)
    ≈ rig_add R (rig_add R a d) (rig_add R b c).
Proof.
  rewrite (rig_add_assoc R a b (rig_add R c d)).
  rewrite <- (rig_add_assoc R b c d).
  rewrite (rig_add_comm R (rig_add R b c) d).
  rewrite <- (rig_add_assoc R a d (rig_add R b c)).
  reflexivity.
Qed.

(* a+(b+c) ≈ b+(c+a) -- the cyclic rotation the Jacobi cancellation
   needs. *)
Lemma lie_add_rot (R : RigObject) (a b c : carrier (rig_setoid R)) :
  rig_add R a (rig_add R b c) ≈ rig_add R b (rig_add R c a).
Proof.
  rewrite <- (rig_add_assoc R a b c).
  rewrite (rig_add_comm R a b).
  rewrite (rig_add_assoc R b a c).
  rewrite (rig_add_comm R a c).
  reflexivity.
Qed.

(* The whole Jacobi cancellation, with the six triple products replaced
   by bare variables.  It is APPLIED, never rewritten with, so no
   rewrite in [lie_comm_jacobi] has to traverse a concrete product. *)
Lemma lie_jacobi_shape (R : RingObject)
  (a b c d e f : carrier (rig_setoid R)) :
  rig_add R
    (rig_add R (rig_add R a f) (ring_neg R (rig_add R b c)))
    (rig_add R
       (rig_add R (rig_add R c b) (ring_neg R (rig_add R d e)))
       (rig_add R (rig_add R e d) (ring_neg R (rig_add R f a))))
  ≈ rig_zero R.
Proof.
  rewrite !lie_sub_plus.
  rewrite (rig_add_comm R a f).
  rewrite (rig_add_comm R c b).
  rewrite (rig_add_comm R e d).
  rewrite (lie_add_rot R (rig_add R f a) (rig_add R b c)
             (rig_add R d e)).
  apply ring_neg_r.
Qed.

(** * The commutator bracket *)

Section Commutator.

Context {K : CRng}.
Context (A : AAlgObject K).

Local Notation RA := (aalg_ring A).
Local Notation UA := (rig_map (aalg_unit A)).

Definition lie_comm_br (x y : carrier (rig_setoid RA))
  : carrier (rig_setoid RA) :=
  rig_add RA (rig_mul RA x y) (ring_neg RA (rig_mul RA y x)).

#[export] Instance lie_comm_br_respects :
  Proper (equiv ==> equiv ==> equiv) lie_comm_br.
Proof.
  intros x x' Hx y y' Hy; unfold lie_comm_br; now rewrite Hx, Hy.
Qed.

(* Additivity in the first slot: [rig_distr_r] then [rig_distr_l], and
   nothing else.  Centrality is NOT consumed. *)
Lemma lie_comm_add_l (x y z : carrier (rig_setoid RA)) :
  lie_comm_br (rig_add RA x y) z
    ≈ rig_add RA (lie_comm_br x z) (lie_comm_br y z).
Proof.
  unfold lie_comm_br.
  rewrite lie_sub_plus.
  rewrite (rig_distr_r RA x y z).
  rewrite (rig_distr_l RA z x y).
  reflexivity.
Qed.

Lemma lie_comm_add_r (x y z : carrier (rig_setoid RA)) :
  lie_comm_br x (rig_add RA y z)
    ≈ rig_add RA (lie_comm_br x y) (lie_comm_br x z).
Proof.
  unfold lie_comm_br.
  rewrite lie_sub_plus.
  rewrite (rig_distr_l RA x y z).
  rewrite (rig_distr_r RA y z x).
  reflexivity.
Qed.

(* THE ONE PLACE CENTRALITY IS SPENT, and it is spent once: the rewrite
   with [aalg_central] moves u(r) back across y in y·(u(r)·x). *)
Lemma lie_comm_smul_l r (x y : carrier (rig_setoid RA)) :
  lie_comm_br (rig_mul RA (UA r) x) y
    ≈ rig_mul RA (UA r) (lie_comm_br x y).
Proof.
  unfold lie_comm_br.
  rewrite (rig_distr_l RA (UA r) (rig_mul RA x y)
             (ring_neg RA (rig_mul RA y x))).
  rewrite lie_mul_neg_r.
  rewrite (rig_mul_assoc RA (UA r) x y).
  rewrite <- (rig_mul_assoc RA y (UA r) x).
  rewrite <- (aalg_central A r y).
  rewrite (rig_mul_assoc RA (UA r) y x).
  reflexivity.
Qed.

(* Alternating: one line, and it is the additive inverse law alone. *)
Lemma lie_comm_alt (x : carrier (rig_setoid RA)) :
  lie_comm_br x x ≈ rig_zero RA.
Proof. unfold lie_comm_br; apply ring_neg_r. Qed.

(* [x,[y,z]] expanded into two positive and two negative right-
   associated triple products.  Associativity of multiplication is spent
   twice; centrality is not spent at all. *)
Lemma lie_comm_triple (x y z : carrier (rig_setoid RA)) :
  lie_comm_br x (lie_comm_br y z)
    ≈ rig_add RA
        (rig_add RA (rig_mul RA x (rig_mul RA y z))
                    (rig_mul RA z (rig_mul RA y x)))
        (ring_neg RA
           (rig_add RA (rig_mul RA x (rig_mul RA z y))
                       (rig_mul RA y (rig_mul RA z x)))).
Proof.
  unfold lie_comm_br.
  rewrite (rig_distr_l RA x (rig_mul RA y z)
             (ring_neg RA (rig_mul RA z y))).
  rewrite (lie_mul_neg_r RA x (rig_mul RA z y)).
  rewrite (rig_distr_r RA (rig_mul RA y z)
             (ring_neg RA (rig_mul RA z y)) x).
  rewrite (lie_mul_neg_l RA (rig_mul RA z y) x).
  rewrite (rig_mul_assoc RA y z x).
  rewrite (rig_mul_assoc RA z y x).
  rewrite (ring_neg_add RA (rig_mul RA y (rig_mul RA z x))
             (ring_neg RA (rig_mul RA z (rig_mul RA y x)))).
  rewrite (ring_neg_involutive RA (rig_mul RA z (rig_mul RA y x))).
  rewrite (ring_neg_add RA (rig_mul RA x (rig_mul RA z y))
             (rig_mul RA y (rig_mul RA z x))).
  apply lie_add_shuffle4.
Qed.

(* Jacobi: three instances of [lie_comm_triple] and one application of
   [lie_jacobi_shape].  The six triple products line up with the shape
   lemma's six variables on the nose. *)
Lemma lie_comm_jacobi (x y z : carrier (rig_setoid RA)) :
  rig_add RA (lie_comm_br x (lie_comm_br y z))
    (rig_add RA (lie_comm_br y (lie_comm_br z x))
                (lie_comm_br z (lie_comm_br x y)))
    ≈ rig_zero RA.
Proof.
  rewrite (lie_comm_triple x y z).
  rewrite (lie_comm_triple y z x).
  rewrite (lie_comm_triple z x y).
  apply lie_jacobi_shape.
Qed.

End Commutator.

Arguments lie_comm_br {K} _ _ _.

(** ** The commutator Lie algebra

    A record literal rather than a [Program Definition]: every field is
    discharged by the matching lemma above, up to conversion between
    [rig_add]/[ring_neg] of the ring and [cmon_plus]/[ab_neg] of the
    module [AAlg_RMod] reads off it.  Writing it this way makes the
    field-to-lemma correspondence visible and raises no obligations. *)
Definition lie_of_aalg {K : CRng} (A : AAlgObject K) : LieObject K := {|
  lie_mod         := AAlg_RMod A;
  lie_br          := lie_comm_br A;
  lie_br_respects := lie_comm_br_respects A;
  lie_br_add_l    := lie_comm_add_l A;
  lie_br_add_r    := lie_comm_add_r A;
  lie_br_smul_l   := lie_comm_smul_l A;
  lie_alt         := lie_comm_alt A;
  lie_jacobi      := lie_comm_jacobi A
|}.

(* THE UNDERLYING MODULE IS UNTOUCHED, on the nose. *)
Example lie_comm_underlying {K : CRng} (A : AAlg K) :
  lie_mod (lie_of_aalg A) = fobj[AAlg_Forget_Mod K] A := eq_refl.

Example lie_comm_bracket_is_comm {K : CRng} (A : AAlgObject K)
  (x y : carrier (rig_setoid (aalg_ring A))) :
  lie_br (lie_of_aalg A) x y = lie_comm_br A x y := eq_refl.

(** ** The commutator of a morphism *)

Lemma lie_comm_map {K : CRng} {A B : AAlgObject K} (f : AAlgHom A B)
  (x y : carrier (rig_setoid (aalg_ring A))) :
  rig_map (`1 f) (lie_comm_br A x y)
    ≈ lie_comm_br B (rig_map (`1 f) x) (rig_map (`1 f) y).
Proof.
  unfold lie_comm_br.
  rewrite (rig_map_add (`1 f)).
  rewrite (RigHom_neg (aalg_ring A) (aalg_ring B) (`1 f)).
  rewrite !(rig_map_mul (`1 f)).
  reflexivity.
Qed.

Definition lie_hom_of_aalg {K : CRng} {A B : AAlgObject K}
  (f : AAlgHom A B) : LieHom (lie_of_aalg A) (lie_of_aalg B) :=
  @Build_LieHom K (lie_of_aalg A) (lie_of_aalg B)
    (AAlg_RModHom f) (lie_comm_map f).

(** ** Mac Lane's V *)

Program Definition CommutatorFunctor (K : CRng) : AAlg K ⟶ Lie K := {|
  fobj := @lie_of_aalg K;
  fmap := fun A B f => lie_hom_of_aalg f
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(* Both data fields of the two forgetful composites agree on the nose;
   the whole functor records do NOT, and the probe section pins that. *)
Example lie_forget_compose_obj {K : CRng} (A : AAlg K) :
  fobj[Lie_Forget_Mod K] (fobj[CommutatorFunctor K] A)
    = fobj[AAlg_Forget_Mod K] A := eq_refl.

Example lie_forget_compose_map {K : CRng} {A B : AAlg K} (f : A ~> B) :
  fmap[Lie_Forget_Mod K] (fmap[CommutatorFunctor K] f)
    = fmap[AAlg_Forget_Mod K] f := eq_refl.

Example lie_comm_fmap_mod {K : CRng} {A B : AAlgObject K}
  (f : AAlgHom A B) :
  lie_hom (lie_hom_of_aalg f) = AAlg_RModHom f := eq_refl.

Example lie_comm_underlying_set {K : CRng} (A : AAlg K) :
  fobj[Lie_Forget K] (fobj[CommutatorFunctor K] A)
    = fobj[AAlg_Forget K] A := eq_refl.

Example lie_comm_forget_set {K : CRng} (L : Lie K) :
  fobj[Lie_Forget K] L = fobj[RMod_Forget (`1 K)] (fobj[Lie_Forget_Mod K] L)
  := eq_refl.

(** ** The commutator functor is faithful, and is not full *)

#[export] Instance CommutatorFunctor_Faithful (K : CRng) :
  Faithful (CommutatorFunctor K).
Proof. constructor; intros A B f g E; exact E. Qed.

(* The zero map is a Lie homomorphism between ANY two Lie algebras: it
   is a module map, and the bracket clause reads 0 ≈ [0,0], which is
   [lie_br_zero_l]. *)
Program Definition lie_zero_hom {K : CRng} (L M : LieObject K)
  : LieHom L M := {|
  lie_hom := {| rm_hom := {| cmon_map :=
                  {| morphism := fun _ => cmon_zero (lie_mod M) |} |} |}
|}.
Next Obligation. intros K L M x y H; reflexivity. Qed.
Next Obligation. intros K L M; reflexivity. Qed.
Next Obligation.
  intros K L M a b; simpl; symmetry; apply (cmon_plus_zero_l (lie_mod M)).
Qed.
Next Obligation.
  intros K L M r m; simpl; symmetry; apply (rm_smul_zero_r (lie_mod M) r).
Qed.
Next Obligation.
  intros K L M x y; simpl; symmetry; apply (lie_br_zero_l M).
Qed.

(** * A Lie algebra with a provably nonzero bracket

    [UT2] (Associative.v) is the ring of upper-triangular 2x2 integer
    matrices, carried as Z-triples with LEIBNIZ equality for its
    hom-setoid, so every bracket below COMPUTES and the negatives are
    settled by [discriminate].  By [lie_comm_of_commutative] a
    commutative ring could not have served; [UT2] is NOT the only
    non-commutative one in the tree, and the header says which others
    there are and why the computing hom-setoid is what selects this
    one. *)

Definition Lie_UT2 : LieObject Int_CRng := lie_of_aalg UT2_AAlg.

Example lie_ut2_carrier : carrier (cmon_setoid (lie_mod Lie_UT2)) = ut2
  := eq_refl.

(* [E11, E12] = E11·E12 - E12·E11 = E12 - 0 = E12. *)
Example lie_ut2_e11_e12 :
  lie_br Lie_UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

(* ...and the other order is its negative, computed. *)
Example lie_ut2_e12_e11 :
  lie_br Lie_UT2 ut2_e12 ut2_e11 = (0, -1, 0)%Z := eq_refl.

Theorem lie_ut2_bracket_nonzero :
  lie_br Lie_UT2 ut2_e11 ut2_e12 ≈ cmon_zero (lie_mod Lie_UT2) → False.
Proof. unfold ut2_eqT; simpl; discriminate. Qed.

(* Non-degenerate in the sharper sense too: the bracket is not symmetric,
   so [Lie_UT2] is not the abelian Lie algebra on its own module in
   disguise. *)
Theorem lie_ut2_not_abelian :
  lie_br Lie_UT2 ut2_e11 ut2_e12 ≈ lie_br Lie_UT2 ut2_e12 ut2_e11 → False.
Proof. unfold ut2_eqT; simpl; discriminate. Qed.

(* Hence no theorem of this file can force brackets to vanish. *)
Theorem lie_not_all_abelian :
  (∀ (L : LieObject Int_CRng) x y,
     lie_br L x y ≈ cmon_zero (lie_mod L)) → False.
Proof.
  intro H.
  exact (lie_ut2_bracket_nonzero (H Lie_UT2 ut2_e11 ut2_e12)).
Qed.

(** ** Non-fullness

    The zero endomorphism of [Lie_UT2] is a Lie map; it is the image of
    no algebra map, because an algebra map carries 1 to 1 and [UT2] has
    1 ≉ 0. *)

Lemma lie_ut2_one_not_zero : rig_one UT2 ≈ rig_zero UT2 → False.
Proof. unfold ut2_eqT; simpl; discriminate. Qed.

Theorem CommutatorFunctor_not_Full : Full (CommutatorFunctor Int_CRng) → False.
Proof.
  intro HF.
  pose proof (@fmap_sur _ _ (CommutatorFunctor Int_CRng) HF
                UT2_AAlg UT2_AAlg (lie_zero_hom Lie_UT2 Lie_UT2)) as Hs.
  apply lie_ut2_one_not_zero.
  rewrite <- (rig_map_one (`1 (@prefmap _ _ (CommutatorFunctor Int_CRng) HF
                UT2_AAlg UT2_AAlg (lie_zero_hom Lie_UT2 Lie_UT2)))).
  exact (Hs (rig_one UT2)).
Qed.

(** ** The commutative case is the degenerate one *)

Theorem lie_comm_of_commutative {K : CRng} (A : AAlgObject K)
  (Hc : ∀ a b, rig_mul (aalg_ring A) a b ≈ rig_mul (aalg_ring A) b a)
  (x y : carrier (rig_setoid (aalg_ring A))) :
  lie_br (lie_of_aalg A) x y ≈ cmon_zero (lie_mod (lie_of_aalg A)).
Proof.
  simpl; unfold lie_comm_br.
  rewrite (Hc y x).
  apply ring_neg_r.
Qed.

Example lie_base_int_bracket (a b : carrier (rig_setoid Int_Ring)) :
  lie_br (lie_of_aalg (Base_AAlg Int_CRng)) a b
    ≈ cmon_zero (lie_mod (lie_of_aalg (Base_AAlg Int_CRng))).
Proof. apply lie_comm_of_commutative; intros p q; apply Z.mul_comm. Qed.

(** * Probes

    Each negative is stated beside an APPLIED positive control, and each
    was stripped ONE AT A TIME and compiled alone so that its failure is
    read off its own command rather than inherited from an earlier one.
    Kinds are kept lexically apart and are classified from the WHOLE
    error message.

    Negative 1 (CONVERSION).  The two forgetful composites are not the
    same functor record, although both data fields agree by [eq_refl]
    ([lie_forget_compose_obj], [lie_forget_compose_map], restated as the
    controls).  [Compose] rebuilds [fmap_respects], [fmap_id] and
    [fmap_comp] as its own opaque obligations, so the difference is
    confined to those three law fields.

    Negative 2 (CONVERSION).  The bracket of a commutative algebra is
    [≈] zero and not [=] zero, even over ℤ where the multiplication
    computes: [a*b + -(b*a)] is stuck at variable a and b.  The control
    is the [≈] statement at the same arguments.

    Negative 3 (TYPING).  A bare module homomorphism is not a [LieHom]:
    the bracket clause is genuine data, not a property recoverable from
    the module map.  The control builds the same [LieHom] with the
    clause supplied.

    Negative 4 (TYPING).  The carrier of a module does not determine the
    Lie structure on it, so the [LieObject] argument of [lie_br] cannot
    be recovered from its two element arguments.  READ THE MESSAGE
    RATHER THAN THE INTENT: this is NOT the "Cannot infer this
    placeholder" report one might expect, and it was classified
    RESOLUTION in a first draft on that expectation.  Elaboration fails
    at the ELEMENT argument, reporting

      The term "ut2_e11" has type "ut2" while it is expected to have
      type "carrier (lie_mod ?l)"

    -- a plain mismatch with the hole still visible in the expected
    type, and with no "cannot unify" clause -- so the hole is never
    reached as a placeholder to be solved.  That is also the content:
    [ut2] carries no trace of the bracket, and the control succeeds only
    because supplying [Lie_UT2] lets [carrier (lie_mod Lie_UT2)] reduce
    to [ut2].

    NO FORMABILITY (universe) AND NO RESOLUTION NEGATIVE IS DELIVERED,
    and neither absence is an oversight: this file declares no universe
    binder and inspects no constraint block, and every elaboration below
    that could fail does so on a type mismatch before any instance or
    placeholder is left outstanding.  Two of the four negatives are
    CONVERSION and two are TYPING.

    Instrument check: a name that exists nowhere, so the [Fail]
    mechanism itself is exercised without reference to any constant
    declared here. *)

(* Negative 1 -- CONVERSION. *)
Fail Example lie_probe_forget_strict (K : CRng) :
  Lie_Forget_Mod K ◯ CommutatorFunctor K = AAlg_Forget_Mod K := eq_refl.

Example lie_probe_forget_obj_ctrl (K : CRng) (A : AAlg K) :
  fobj[Lie_Forget_Mod K ◯ CommutatorFunctor K] A
    = fobj[AAlg_Forget_Mod K] A := eq_refl.

Example lie_probe_forget_map_ctrl (K : CRng) (A B : AAlg K) (f : A ~> B) :
  fmap[Lie_Forget_Mod K ◯ CommutatorFunctor K] f
    = fmap[AAlg_Forget_Mod K] f := eq_refl.

(* Negative 2 -- CONVERSION. *)
Fail Example lie_probe_commutative_strict
  (a b : carrier (rig_setoid Int_Ring)) :
  lie_br (lie_of_aalg (Base_AAlg Int_CRng)) a b = rig_zero Int_Ring
  := eq_refl.

Example lie_probe_commutative_ctrl (a b : carrier (rig_setoid Int_Ring)) :
  lie_br (lie_of_aalg (Base_AAlg Int_CRng)) a b ≈ rig_zero Int_Ring.
Proof. apply lie_comm_of_commutative; intros p q; apply Z.mul_comm. Qed.

(* Negative 3 -- TYPING. *)
Fail Definition lie_probe_hom_needs_bracket
  (L M : LieObject Int_CRng) (f : RModHom (lie_mod L) (lie_mod M))
  : LieHom L M := f.

Definition lie_probe_hom_ctrl (L M : LieObject Int_CRng)
  (f : RModHom (lie_mod L) (lie_mod M))
  (Hb : ∀ x y, cmon_map (rm_hom f) (lie_br L x y)
                 ≈ lie_br M (cmon_map (rm_hom f) x)
                            (cmon_map (rm_hom f) y))
  : LieHom L M := @Build_LieHom Int_CRng L M f Hb.

(* Negative 4 -- TYPING. *)
Fail Check (@lie_br Int_CRng _ ut2_e11 ut2_e12).

Check (@lie_br Int_CRng Lie_UT2 ut2_e11 ut2_e12).

(* Instrument check. *)
Fail Check lie_probe_instrument_absent.
