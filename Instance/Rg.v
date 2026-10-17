Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/rng
 nLab: https://ncatlab.org/nlab/show/nonunital+ring
 Wikipedia: https://en.wikipedia.org/wiki/Rng_(algebra)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Rngs over a setoid carrier *)

(* An abelian group with an associative, doubly distributive
   multiplication.  No unit, and no annihilation clause: the latter is
   derivable here, which is exactly the difference from [RigObject]. *)
Record RgObject := {
  rg_ab :> AbObject;

  rg_mul : carrier (cmon_setoid (ab_cmon rg_ab)) →
           carrier (cmon_setoid (ab_cmon rg_ab)) →
           carrier (cmon_setoid (ab_cmon rg_ab));

  rg_mul_respects : Proper (equiv ==> equiv ==> equiv) rg_mul;

  rg_mul_assoc : ∀ a b c,
    rg_mul (rg_mul a b) c ≈ rg_mul a (rg_mul b c);

  rg_distr_l : ∀ a b c,
    rg_mul a (cmon_plus (ab_cmon rg_ab) b c)
      ≈ cmon_plus (ab_cmon rg_ab) (rg_mul a b) (rg_mul a c);
  rg_distr_r : ∀ a b c,
    rg_mul (cmon_plus (ab_cmon rg_ab) a b) c
      ≈ cmon_plus (ab_cmon rg_ab) (rg_mul a c) (rg_mul b c)
}.

#[export] Existing Instance rg_mul_respects.

(** ** Annihilation, derived *)

(* In an abelian group an element that is its own double is zero.  This
   is the elementary counterpart of Structure/Ring.v's
   [ring_cancel_idem], and it is the whole content of the two
   annihilation laws below. *)
Lemma rg_cancel_idem (A : AbObject) (k : carrier (cmon_setoid A)) :
  cmon_plus A k k ≈ k → k ≈ cmon_zero A.
Proof.
  intro H.
  transitivity (cmon_plus A (ab_neg A k) (cmon_plus A k k)).
  - rewrite <- cmon_plus_assoc.
    rewrite ab_neg_left.
    now rewrite cmon_plus_zero_l.
  - rewrite H.
    apply ab_neg_left.
Qed.

(* 0·a = (0 + 0)·a = 0·a + 0·a, so 0·a is idempotent, so it is 0.  The
   corresponding clauses of [RigObject] are FIELDS; here they are
   theorems, and Structure/Ring.v's [bool_or_not_annihilating] is
   why a rig cannot do the same. *)
Lemma rg_mul_zero_l (R : RgObject) (a : carrier (cmon_setoid (rg_ab R))) :
  rg_mul R (cmon_zero (rg_ab R)) a ≈ cmon_zero (rg_ab R).
Proof.
  apply (rg_cancel_idem (rg_ab R)).
  rewrite <- rg_distr_r.
  now rewrite cmon_plus_zero_l.
Qed.

Lemma rg_mul_zero_r (R : RgObject) (a : carrier (cmon_setoid (rg_ab R))) :
  rg_mul R a (cmon_zero (rg_ab R)) ≈ cmon_zero (rg_ab R).
Proof.
  apply (rg_cancel_idem (rg_ab R)).
  rewrite <- rg_distr_l.
  now rewrite cmon_plus_zero_l.
Qed.

(** ** Homomorphisms *)

(* A rng homomorphism is a homomorphism of the additive abelian groups
   that also respects multiplication.  There is no unit clause, and that
   single omission is what separates this category from [Rng]. *)
Record RgHom (R S : RgObject) := {
  rg_hom_ab :> AbHom R S;

  rg_map_mul : ∀ a b,
    cmon_map rg_hom_ab (rg_mul R a b)
      ≈ rg_mul S (cmon_map rg_hom_ab a) (cmon_map rg_hom_ab b)
}.

Arguments rg_hom_ab {R S} _.
Arguments rg_map_mul {R S} _ _ _.

(* Preservation of negation is NOT a field and is NOT proved here: it is
   Instance/Ab.v's [ab_map_neg], applied.  The unital-side twin is
   Theory/Algebra/Rig.v's [RigHom_neg]. *)
Corollary rg_map_neg {R S : RgObject} (f : RgHom R S)
  (a : carrier (cmon_setoid (rg_ab R))) :
  cmon_map (rg_hom_ab f) (ab_neg (rg_ab R) a)
    ≈ ab_neg (rg_ab S) (cmon_map (rg_hom_ab f) a).
Proof. exact (ab_map_neg (rg_hom_ab f) a). Qed.

#[local] Obligation Tactic := idtac.

(* Homomorphisms are compared by their underlying maps, pointwise —
   Theory/Algebra/Rig.v's [RigHom_Setoid] pattern. *)
#[export]
Program Instance RgHom_Setoid {R S : RgObject} : Setoid (RgHom R S) := {|
  equiv := fun f g => ∀ a, cmon_map (rg_hom_ab f) a
                             ≈ cmon_map (rg_hom_ab g) a
|}.
Next Obligation.
  intros R S.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map (rg_hom_ab g) a); [ apply Hfg | apply Hgh ].
Qed.

Program Definition rg_hom_id {R : RgObject} : RgHom R R := {|
  rg_hom_ab := @cmon_hom_id (ab_cmon (rg_ab R))
|}.
Next Obligation. intros R a b; simpl; reflexivity. Qed.

Program Definition rg_hom_compose {R S T : RgObject}
  (f : RgHom S T) (g : RgHom R S) : RgHom R T := {|
  rg_hom_ab := cmon_hom_compose (rg_hom_ab f) (rg_hom_ab g)
|}.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (cmon_map (rg_hom_ab f)) _ _
             (rg_map_mul g a b)).
  apply rg_map_mul.
Qed.

Lemma rg_hom_compose_respects {R S T : RgObject} :
  Proper (equiv ==> equiv ==> equiv) (@rg_hom_compose R S T).
Proof.
  intros f1 f2 Hf g1 g2 Hg a; simpl.
  rewrite (Hf (cmon_map (rg_hom_ab g1) a)).
  apply (proper_morphism (cmon_map (rg_hom_ab f2))), Hg.
Qed.

(** ** The category *)

(* The universes are pinned by hand, for the reason recorded at
   Instance/CMon.v's [CMon]: with [cmon_prop] a field of the underlying
   [CMonObject] the record sort carries a [Set+1], and left to itself the
   elaborator gives [Rg] a third, redundant universe -- refusing the
   `Rg@{u o}` annotations in this file for arity. *)
Program Definition Rg@{u p} : Category@{u p p} := {|
  obj     := RgObject@{p p p};
  hom     := RgHom@{p};
  homset  := @RgHom_Setoid@{p};
  id      := @rg_hom_id@{p};
  compose := @rg_hom_compose@{u p};

  compose_respects := @rg_hom_compose_respects@{u p}
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** ** Forgetting from Rg *)

Program Definition Rg_Forget_Ab : Rg ⟶ Ab := {|
  fobj := rg_ab;
  fmap := fun R S f => rg_hom_ab f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

Program Definition Rg_Forget : Rg ⟶ Sets := {|
  fobj := fun R : RgObject => cmon_setoid (ab_cmon (rg_ab R));
  fmap := fun R S f => cmon_map (rg_hom_ab f)
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

#[export] Program Instance Rg_Forget_Ab_Faithful : Faithful Rg_Forget_Ab.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.

(** ** The forgetful functor from unital rings *)

(* Pure reuse.  Instance/Rng.v's [ring_ab] already extracts the
   additive abelian group of a unital ring, and every remaining field is
   the corresponding [RigObject] field passed through unchanged — the
   two records' field types are convertible, so not one of the five
   assignments needs a tactic. *)
Definition ring_rg (R : RingObject) : RgObject := {|
  rg_ab := ring_ab R;
  rg_mul := rig_mul R;
  rg_mul_respects := rig_mul_respects R;
  rg_mul_assoc := rig_mul_assoc R;
  rg_distr_l := rig_distr_l R;
  rg_distr_r := rig_distr_r R
|}.

(* The arrow action is Instance/Rng.v's [Rng_Forget_Ab] repackaged
   with one extra field, [rig_map_mul], again passed through unchanged. *)
Program Definition Rng_Forget_Rg : Rng ⟶ Rg := {|
  fobj := ring_rg;
  fmap := fun R S f => {|
    rg_hom_ab := {|
      cmon_map := rig_map f;
      cmon_map_zero := rig_map_zero f;
      cmon_map_plus := rig_map_add f
    |};
    rg_map_mul := rig_map_mul f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(* Faithfulness is CHEAP, and it is worth saying why rather than
   presenting it as work: both hom-setoids compare homomorphisms by
   their underlying maps pointwise, and the forgetful functor leaves the
   underlying map alone, so the hypothesis IS the conclusion. *)
#[export] Program Instance Rng_Forget_Rg_Faithful : Faithful Rng_Forget_Rg.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.

(** ** The functor is not full *)

(* The constant-zero map is a rng homomorphism between ANY two rngs: it
   preserves 0 outright, preserves + because 0 + 0 ≈ 0, and preserves ·
   by [rg_mul_zero_l].  It is not a unital homomorphism unless the
   codomain is trivial, and that is the whole obstruction to fullness. *)
Program Definition rg_zero_mor (R S : RgObject) : RgHom R S := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun _ => cmon_zero (ab_cmon (rg_ab S)) |}
  |}
|}.
Next Obligation. intros R S x y Hxy; reflexivity. Qed.
Next Obligation. intros R S; simpl; reflexivity. Qed.
Next Obligation.
  intros R S a b; simpl; symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R S a b; simpl; symmetry; apply rg_mul_zero_l.
Qed.

(* The zero endomorphism of ℤ in [Rg] has no unital preimage: any
   [RigHom] out of ℤ sends 1 to 1, and the zero map sends 1 to 0. *)
Theorem Rng_Forget_Rg_not_Full : Full Rng_Forget_Rg → False.
Proof.
  intro F.
  pose (z := rg_zero_mor (ring_rg Int_Ring) (ring_rg Int_Ring)).
  pose (g := @prefmap _ _ _ F Int_Ring Int_Ring z).
  assert (H0 : rig_map g 1%Z = 0%Z)
    by exact (@fmap_sur _ _ _ F Int_Ring Int_Ring z 1%Z).
  assert (H1 : rig_map g 1%Z = 1%Z) by exact (rig_map_one g).
  rewrite H0 in H1.
  discriminate.
Qed.

(** ** The trivial rng is a zero object *)

(* Built on Instance/CMon/Biproduct.v's polymorphic [CMon_trivial],
   NOT on Instance/Ab.v's [Ab_trivial], which is measured to be
   [AbObject@{Set Set Set}] with no universe binders at all. *)
Definition rg_trivial_ab@{o} : AbObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial@{o};
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

Definition Rg_trivial@{o} : RgObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    rg_ab  := rg_trivial_ab@{o};
    rg_mul := fun _ _ => ttt
  |}.
  - intros x y Hxy u v Huv; reflexivity.
  - intros a b c; reflexivity.
  - intros a b c; reflexivity.
  - intros a b c; reflexivity.
Defined.

(* Terminal: everything to the point. *)
Program Definition Rg_one@{u o} (R : RgObject@{o o o})
  : R ~{Rg@{u o}}~> Rg_trivial@{o} := {|
  rg_hom_ab := {| cmon_map := {| morphism := fun _ => ttt |} |}
|}.
Next Obligation. intros R x y Hxy; reflexivity. Qed.
Next Obligation. intros R; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.

Lemma Rg_one_unique@{u o} (R : RgObject@{o o o})
  (f : R ~{Rg@{u o}}~> Rg_trivial@{o}) : f ≈ Rg_one@{u o} R.
Proof.
  intro a; simpl.
  destruct (cmon_map (rg_hom_ab f) a); reflexivity.
Qed.

#[export] Program Instance Rg_Terminal : @Terminal Rg := {|
  terminal_obj := Rg_trivial;
  one          := Rg_one
|}.
Next Obligation.
  intros R f g.
  now rewrite (Rg_one_unique R f), (Rg_one_unique R g).
Qed.

(* Initial: the point goes to zero.  This is the SECOND of the two
   places the derived annihilation law is spent (the first is
   [rg_zero_mor] above) — the multiplicativity obligation reads
   [0 ≈ rg_mul R 0 0], which is exactly [rg_mul_zero_l].  On the unital
   side the corresponding morphism does not exist at all, which is what
   [Rng_terminal_not_initial] below records. *)
Program Definition Rg_zero_hom@{u o} (R : RgObject@{o o o})
  : Rg_trivial@{o} ~{Rg@{u o}}~> R := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun _ => cmon_zero (ab_cmon (rg_ab R)) |}
  |}
|}.
Next Obligation. intros R x y Hxy; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation.
  intros R a b; simpl; symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R a b; simpl; symmetry; apply rg_mul_zero_l.
Qed.

Lemma Rg_zero_hom_unique@{u o} (R : RgObject@{o o o})
  (f : Rg_trivial@{o} ~{Rg@{u o}}~> R) : f ≈ Rg_zero_hom@{u o} R.
Proof.
  intro a; destruct a; simpl.
  exact (cmon_map_zero (rg_hom_ab f)).
Qed.

#[export] Program Instance Rg_Initial : @Initial Rg := {|
  terminal_obj := Rg_trivial : obj[Rg^op];
  one          := Rg_zero_hom
|}.
Next Obligation.
  intros R f g.
  now rewrite (Rg_zero_hom_unique R f), (Rg_zero_hom_unique R g).
Qed.

(* One record plays both roles, so the coincidence isomorphism is the
   identity — Instance/CMon/Biproduct.v and Instance/Ab.v do the
   same. *)
#[export] Instance Rg_Zero : ZeroObject Rg :=
  @Build_ZeroObject Rg Rg_Terminal Rg_Initial iso_id.

(** ** The contrast with the unital category *)

(* On the unital side no morphism runs from the terminal object to the
   initial one: such a morphism would carry the zero ring's 1 — which is
   also its 0 — to both 1 and 0 in ℤ.

   This is the same fact as Structure/Kernel/Universal/Examples.v's
   [Rng_no_hom_zero_to_Z], restated here under a fresh name rather than
   cited, because requiring that module would pull its 23-module closure
   onto every consumer of [Rg].  No novelty is claimed for it. *)
Theorem Rng_terminal_not_initial :
  (Zero_Ring ~{Rng}~> Int_Ring) → False.
Proof.
  intro f.
  assert (H1 : rig_map f ttt = 1%Z) by exact (rig_map_one f).
  assert (H0 : rig_map f ttt = 0%Z) by exact (rig_map_zero f).
  rewrite H1 in H0.
  discriminate.
Qed.

(* The discriminating pair Instance/Roster.v defers.  Dropping
   unit-preservation from the morphisms changes the answer.  Read the
   TYPE precisely: the second component is "no unital homomorphism from
   the zero ring to Z", which is what forces terminal and initial apart
   in [Rng]; the packaged statement "[Rng] has no zero object" is
   Structure/Kernel/Universal/Examples.v's [Rng_no_zero_object],
   proved there and not repackaged here. *)
Definition Rng_Rg_zero_object_contrast :
  ZeroObject Rg * ((Zero_Ring ~{Rng}~> Int_Ring) → False) :=
  (Rg_Zero, Rng_terminal_not_initial).

(** ** Strict readbacks *)

Example rg_forget_ab_strict (R : RingObject) :
  rg_ab (ring_rg R) = ring_ab R := eq_refl.

Example rg_forget_mul_strict (R : RingObject) :
  rg_mul (ring_rg R) = rig_mul R := eq_refl.

Example rg_forget_carrier_strict (R : RingObject) :
  carrier (cmon_setoid (ab_cmon (rg_ab (ring_rg R))))
    = carrier (rig_setoid R) := eq_refl.

Example rg_forget_zero_strict (R : RingObject) :
  cmon_zero (ab_cmon (rg_ab (ring_rg R))) = rig_zero R := eq_refl.

Example rg_zero_obj_strict :
  @zero_obj Rg Rg_Zero = Rg_trivial := eq_refl.

Example rg_trivial_carrier_strict :
  carrier (cmon_setoid (ab_cmon (rg_ab Rg_trivial))) = poly_unit := eq_refl.

(** ** Two refuted strict attempts, pinned *)

(* The image of the zero ring is a one-element rng, and so is
   [Rg_trivial], but they are not the same record: Instance/Rng.v
   gives [Zero_Rig] the always-true setoid while [CMon_trivial] carries
   Leibniz [eq] on [poly_unit].  The carriers DO agree, which is the
   control, so the failure is located in the [is_setoid] field. *)
Fail Definition probe_zero_ring_is_trivial :
  ring_rg Zero_Ring = Rg_trivial := eq_refl.

Example control_zero_ring_carrier :
  carrier (cmon_setoid (ab_cmon (rg_ab (ring_rg Zero_Ring))))
    = carrier (cmon_setoid (ab_cmon (rg_ab Rg_trivial))) := eq_refl.

(* The forgetful functor does not return the hom RECORD it was given.
   This negative is of a DIFFERENT KIND from the one above, and the kind
   was read off the stripped error rather than guessed: this one reports
   a plain type mismatch with NO [cannot unify] clause, the two records
   living in different hom-sets, whereas the one above does report
   [cannot unify] between two terms of a single type.  The control below
   shows the underlying MAP does survive on the nose. *)
Fail Definition probe_forget_hom_record (R S : RingObject)
  (f : R ~{Rng}~> S) : fmap[Rng_Forget_Rg] f = f := eq_refl.

Example control_forget_underlying_map (R S : RingObject)
  (f : R ~{Rng}~> S) :
  cmon_map (rg_hom_ab (fmap[Rng_Forget_Rg] f)) = rig_map f := eq_refl.

(** ** Non-vacuity: the even integers *)

(* 2ℤ, presented on the carrier ℤ with the multiplication transported
   along z ↦ 2z.  [TwoZ_incl] below proves the presentation earns its
   name.  The three laws are stated first as bare ℤ equations, closed by
   [ring], and then passed to the record by [exact]: the obligation
   types are CONVERTIBLE with them, [Z_eqT] being Leibniz equality, so
   no setoid reasoning is needed and none is done — the same move
   Theory/Algebra/Rig.v makes for [Int_Rig]. *)
Definition TwoZ_mul (a b : Z) : Z := 2 * a * b.

Lemma TwoZ_assoc_Z (a b c : Z) :
  TwoZ_mul (TwoZ_mul a b) c = TwoZ_mul a (TwoZ_mul b c).
Proof. unfold TwoZ_mul; ring. Qed.

Lemma TwoZ_distr_l_Z (a b c : Z) :
  TwoZ_mul a (Z.add b c) = Z.add (TwoZ_mul a b) (TwoZ_mul a c).
Proof. unfold TwoZ_mul; ring. Qed.

Lemma TwoZ_distr_r_Z (a b c : Z) :
  TwoZ_mul (Z.add a b) c = Z.add (TwoZ_mul a c) (TwoZ_mul b c).
Proof. unfold TwoZ_mul; ring. Qed.

(* Note, and it is the hazard CLAUDE.md records for
   Instance/Sets/Products.v: this [Program Definition] raises
   THREE obligations, not four.  The [rg_mul_respects] field is closed
   by instance resolution during elaboration, because [Z_eqT] is
   Leibniz equality and every function is [Proper] for it.  The three
   that remain are [rg_mul_assoc], [rg_distr_l] and [rg_distr_r], in
   that order. *)
Program Definition TwoZ_Rg : RgObject := {|
  rg_ab  := ring_ab Int_Ring;
  rg_mul := TwoZ_mul
|}.
Next Obligation. exact TwoZ_assoc_Z. Qed.
Next Obligation. exact TwoZ_distr_l_Z. Qed.
Next Obligation. exact TwoZ_distr_r_Z. Qed.

(* Not unital: e·1 ≈ 1 reads 2e = 1 in ℤ, which [lia] refutes.  This is
   the whole point of the witness — [Rg] is not secretly [Rng]. *)
Theorem TwoZ_not_unital :
  ∀ e : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg))),
    (∀ a, rg_mul TwoZ_Rg e a ≈ a) → False.
Proof.
  intros e H.
  assert (H1 : TwoZ_mul e 1%Z = 1%Z) by exact (H 1%Z).
  unfold TwoZ_mul in H1.
  lia.
Qed.

(* Not degenerate: the carrier has two distinct elements. *)
Theorem TwoZ_nondegenerate :
  (0%Z : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg))))
    ≈ (1%Z : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg)))) → False.
Proof. intro H; unfold Z_eqT in H; discriminate. Qed.

(* And its multiplication is not identically zero, which is what
   separates this witness from the cheap zero-multiplication rng on an
   arbitrary abelian group: there the multiplicative axioms hold
   vacuously, here they are exercised. *)
Theorem TwoZ_mul_nonzero :
  rg_mul TwoZ_Rg 1%Z 1%Z
    ≈ cmon_zero (ab_cmon (rg_ab TwoZ_Rg)) → False.
Proof. intro H; unfold Z_eqT in H; discriminate. Qed.

(* The name is earned rather than asserted: doubling is an injective rng
   homomorphism into ℤ whose image is exactly the even integers.
   Multiplicativity is the one clause with content, and it is why the
   transported multiplication had to be 2ab —
   d(a ·₂ b) = 2·(2ab) = 4ab = (2a)(2b) = d a · d b. *)
Definition TwoZ_double (z : Z) : Z := 2 * z.

Lemma TwoZ_double_add (a b : Z) :
  TwoZ_double (Z.add a b) = Z.add (TwoZ_double a) (TwoZ_double b).
Proof. unfold TwoZ_double; ring. Qed.

Lemma TwoZ_double_mul (a b : Z) :
  TwoZ_double (TwoZ_mul a b) = Z.mul (TwoZ_double a) (TwoZ_double b).
Proof. unfold TwoZ_double, TwoZ_mul; ring. Qed.

Program Definition TwoZ_incl : RgHom TwoZ_Rg (ring_rg Int_Ring) := {|
  rg_hom_ab := {| cmon_map := {| morphism := TwoZ_double |} |}
|}.
Next Obligation. exact (@eq_refl Z 0%Z). Qed.
Next Obligation. exact TwoZ_double_add. Qed.
Next Obligation. exact TwoZ_double_mul. Qed.

Theorem TwoZ_incl_injective : ∀ a b,
  cmon_map (rg_hom_ab TwoZ_incl) a ≈ cmon_map (rg_hom_ab TwoZ_incl) b →
  a ≈ b.
Proof.
  intros a b H.
  assert (H2 : TwoZ_double a = TwoZ_double b) by exact H.
  unfold TwoZ_double in H2.
  assert (Hab : a = b) by lia.
  exact Hab.
Qed.

Theorem TwoZ_incl_image_even : ∀ a,
  { k : Z & cmon_map (rg_hom_ab TwoZ_incl) a = Z.mul 2 k }.
Proof. intro a; exists a; exact (@eq_refl Z (TwoZ_double a)). Qed.

(* The converse half, without which the word "exactly" would be unearned:
   every even integer IS hit.  The two together say the image is the
   even integers and not merely a subset of them. *)
Theorem TwoZ_incl_image_onto_even : ∀ k : Z,
  { a & cmon_map (rg_hom_ab TwoZ_incl) a = Z.mul 2 k }.
Proof. intro k; exists k; exact (@eq_refl Z (TwoZ_double k)). Qed.

(** ** The universe instance, for the record

    Rerun the commands below to reproduce the measurement quoted in the
    header: neither [Rg_trivial] nor [Rg_Zero] carries [Set]. *)

Set Printing Universes.
About Rg_trivial.
About Rg_Zero.
Unset Printing Universes.
