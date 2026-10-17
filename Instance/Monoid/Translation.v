(** * Translation endofunctors of a monoid, and their adjoints *)

From Coq Require Import Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/monoid
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出翻译/对应。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Block A: the discrete category on a monoid *)

(* The elements of M as objects, its own `≈` as the only identifications.
   [DiscreteSetoidCat] is Construction/Comma/Special.v, reused rather
   than rebuilt.  That file also explains why Instance/Proset.v's [Proset]
   was not the construction it wanted: [Proset] is stated over `Prop`-valued
   relations while `≈` is a `crelation`.  A `Prop`-squashed variant would in
   any case not obviously support the converse below, which reads an honest
   `≈` OUT of a hom-set — but that is an argument, not a measurement, and no
   squashed variant is built here. *)
Definition MonDiscrete (M : MonObject) : Category :=
  DiscreteSetoidCat (@is_setoid (mon_setoid M)).

Example mon_discrete_obj (M : MonObject) :
  obj[MonDiscrete M] = carrier M := eq_refl.

Example mon_discrete_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

(* Thin: the hom-setoid identifies all parallel arrows.  This is what makes
   every law in Blocks B and D free — NOT those of the strict Block F, whose
   hom-setoid is strict equality of proofs — and it is [DiscreteSetoidCat]'s
   own property. *)
Lemma MonDiscrete_thin (M : MonObject) (x y : MonDiscrete M)
  (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(** ** Block B: multiplication as a bifunctor, and the translations *)

#[local] Obligation Tactic := repeat intro; exact I.

(* Mac Lane's "multiplication as a bifunctor": a functor from the product of
   the discrete category with itself.  Its arrow action IS [mon_op_respects],
   the field that makes multiplication respect `≈`. *)
Program Definition MonMult (M : MonObject) :
  MonDiscrete M ∏ MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun p => mon_op (fst p) (snd p);
  fmap := fun x y f => mon_op_respects M _ _ (fst f) _ _ (snd f)
|}.

Program Definition LeftTranslation (M : MonObject) (a : carrier M) :
  MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun x => mon_op a x;
  fmap := fun x y f => mon_op_respects M a a (reflexivity a) x y f
|}.

Program Definition RightTranslation (M : MonObject) (a : carrier M) :
  MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun x => mon_op x a;
  fmap := fun x y f => mon_op_respects M x y f a a (reflexivity a)
|}.

Example left_translation_obj (M : MonObject) (a x : carrier M) :
  fobj[LeftTranslation M a] x = mon_op a x := eq_refl.

Example right_translation_obj (M : MonObject) (a x : carrier M) :
  fobj[RightTranslation M a] x = mon_op x a := eq_refl.

(* The translations ARE the partial applications of the bifunctor, on both
   data fields, by [eq_refl].  Note the handedness: [Partial_r F b] fixes the
   FIRST argument, so it is LEFT translation. *)
Example lt_partial_obj (M : MonObject) (a : carrier M) :
  fobj[LeftTranslation M a] = fobj[Partial_r (MonMult M) a] := eq_refl.

Example lt_partial_fmap (M : MonObject) (a : carrier M) :
  @fmap _ _ (LeftTranslation M a) = @fmap _ _ (Partial_r (MonMult M) a)
  := eq_refl.

Example rt_partial_obj (M : MonObject) (a : carrier M) :
  fobj[RightTranslation M a] = fobj[Partial_l (MonMult M) a] := eq_refl.

Example rt_partial_fmap (M : MonObject) (a : carrier M) :
  @fmap _ _ (RightTranslation M a) = @fmap _ _ (Partial_l (MonMult M) a)
  := eq_refl.

(** ** Block C: the cancellation calculus of a chosen inverse *)

Section Cancel.
Context (M : MonObject) (Inv : MonInverses M) (a : carrier M).

Lemma mon_inv_cancel_l (x : carrier M) :
  mon_op (minv Inv a) (mon_op a x) ≈ x.
Proof.
  rewrite mon_op_assoc, (minv_l Inv a).
  apply mon_op_unit_l.
Qed.

Lemma mon_inv_cancel_l' (x : carrier M) :
  mon_op a (mon_op (minv Inv a) x) ≈ x.
Proof.
  rewrite mon_op_assoc, (minv_r Inv a).
  apply mon_op_unit_l.
Qed.

Lemma mon_inv_cancel_r (x : carrier M) :
  mon_op (mon_op x a) (minv Inv a) ≈ x.
Proof.
  rewrite <- mon_op_assoc, (minv_r Inv a).
  apply mon_op_unit_r.
Qed.

Lemma mon_inv_cancel_r' (x : carrier M) :
  mon_op (mon_op x (minv Inv a)) a ≈ x.
Proof.
  rewrite <- mon_op_assoc, (minv_l Inv a).
  apply mon_op_unit_r.
Qed.

End Cancel.

(** ** Block D: inversion supplies the right adjoints *)

Section Adjoints.
Context (M : MonObject) (Inv : MonInverses M) (a : carrier M).

(* hom(a·x, y) → hom(x, a⁻¹·y). *)
Definition left_transpose (x y : carrier M) (p : mon_op a x ≈ y) :
  x ≈ mon_op (minv Inv a) y.
Proof.
  rewrite <- (mon_inv_cancel_l M Inv a x).
  now rewrite p.
Defined.

Definition left_untranspose (x y : carrier M)
  (q : x ≈ mon_op (minv Inv a) y) : mon_op a x ≈ y.
Proof.
  rewrite q.
  apply mon_inv_cancel_l'.
Defined.

(* Every remaining field of [Adjunction] — both isomorphism laws, both
   respectfulness proofs and all four naturality clauses — is an equation in
   a hom-setoid of [MonDiscrete M], hence trivially true; the obligation
   tactic in force discharges all eight. *)
Program Definition left_translation_adjunction :
  LeftTranslation M a ⊣ LeftTranslation M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := left_transpose x y |}
     ; from := {| morphism := left_untranspose x y |} |}
|}.

(* hom(x·a, y) → hom(x, y·a⁻¹). *)
Definition right_transpose (x y : carrier M) (p : mon_op x a ≈ y) :
  x ≈ mon_op y (minv Inv a).
Proof.
  rewrite <- (mon_inv_cancel_r M Inv a x).
  now rewrite p.
Defined.

Definition right_untranspose (x y : carrier M)
  (q : x ≈ mon_op y (minv Inv a)) : mon_op x a ≈ y.
Proof.
  rewrite q.
  apply mon_inv_cancel_r'.
Defined.

Program Definition right_translation_adjunction :
  RightTranslation M a ⊣ RightTranslation M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := right_transpose x y |}
     ; from := {| morphism := right_untranspose x y |} |}
|}.

End Adjoints.

(** ** Block E: the converse, and the biconditionals *)

(* The mathematical content of the converse, isolated: a monoid in which
   every element has a right inverse is a group.  With b := r a and
   c := r (r a) we have a·b ≈ 1 and b·c ≈ 1, so [mon_inverse_unique]
   (Construction/Deloop.v) gives a ≈ c, whence b·a ≈ b·c ≈ 1.

   Instance/Grp.v's [grp_mul_inv_r] is the MIRROR IMAGE of this — right
   inverses from left ones — but over that file's own [GrpObject] record, in
   which the inverse operation is a FIELD; it is a different statement over a
   different record, and no attempt is made here to derive either from the
   other. *)
Lemma MonInverses_of_right_inverses (M : MonObject)
  (r : carrier M → carrier M)
  (Hr : ∀ a : carrier M, mon_op a (r a) ≈ mon_unit) : MonInverses M.
Proof.
  refine {| minv := r ; minv_r := Hr |}.
  intro a.
  transitivity (mon_op (r a) (r (r a))).
  - apply mon_op_respects; [reflexivity |].
    exact (mon_inverse_unique M (r a) a (r (r a)) (Hr a) (Hr (r a))).
  - apply Hr.
Defined.

(* The mirror, for the right translations: all left inverses gives a group. *)
Lemma MonInverses_of_left_inverses (M : MonObject)
  (l : carrier M → carrier M)
  (Hl : ∀ a : carrier M, mon_op (l a) a ≈ mon_unit) : MonInverses M.
Proof.
  unshelve refine {| minv := l ; minv_l := Hl |}.
  intro a.
  transitivity (mon_op (l (l a)) (l a)).
  - apply mon_op_respects; [| reflexivity].
    symmetry.
    exact (mon_inverse_unique M (l a) (l (l a)) a (Hl (l a)) (Hl a)).
  - apply Hl.
Defined.

(* "Every left translation has a right adjoint", as DATA.  The library's ∃ is
   [sigT], so this is a function and no choice principle is consumed when the
   inverse operation is read off it. *)
Definition LeftTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & LeftTranslation M a ⊣ R }.

Definition RightTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & RightTranslation M a ⊣ R }.

(* The answer to the exercise's question, in the affirmative.  Forward:
   inversion supplies the adjoints.  Backward: the inverse transpose applied
   to the identity of R(1) is exactly a · R(1) ≈ 1. *)
Theorem mon_group_iff_left_translation_adjoints (M : MonObject) :
  MonInverses M ↔ LeftTranslationAdjoints M.
Proof.
  split.
  - intros Inv a.
    exists (LeftTranslation M (minv Inv a)).
    exact (left_translation_adjunction M Inv a).
  - intro H.
    unshelve refine (MonInverses_of_right_inverses M
      (fun a => fobj[projT1 (H a)] mon_unit) _).
    intro a.
    exact (from (@adj _ _ _ _ (projT2 (H a))
                  (fobj[projT1 (H a)] mon_unit) mon_unit)
             (reflexivity _)).
Defined.

Theorem mon_group_iff_right_translation_adjoints (M : MonObject) :
  MonInverses M ↔ RightTranslationAdjoints M.
Proof.
  split.
  - intros Inv a.
    exists (RightTranslation M (minv Inv a)).
    exact (right_translation_adjunction M Inv a).
  - intro H.
    unshelve refine (MonInverses_of_left_inverses M
      (fun a => fobj[projT1 (H a)] mon_unit) _).
    intro a.
    exact (from (@adj _ _ _ _ (projT2 (H a))
                  (fobj[projT1 (H a)] mon_unit) mon_unit)
             (reflexivity _)).
Defined.

(** ** Block F: the same over [DiscreteCat], where homs are Rocq's `=` *)

(* The two hypotheses, in the shape of Construction/Comma/Special.v's
   [HomStrict] and [HomUIP].  Sufficient for the forward direction below; NOT
   shown necessary. *)
Definition MonStrict (M : MonObject) : Type :=
  ∀ x y : carrier M, x ≈ y → x = y.

Definition MonUIP (M : MonObject) : Type :=
  ∀ (x y : carrier M) (p q : x = y), p = q.

(* Hedberg, via the stdlib's axiom-free [UIP_dec]. *)
Definition MonUIP_dec (M : MonObject)
  (dec : ∀ x y : carrier M, {x = y} + {x <> y}) : MonUIP M := UIP_dec dec.

(* The explicit binders are load-bearing: unannotated, this body minimizes so
   as to identify the hom and proof universes of the result. *)
Definition MonDiscreteStrict@{o h p m1 m2} (M : MonObject@{o m1 m2}) :
  Category@{o h p} := DiscreteCat@{o h p} (carrier M).

Example mon_discrete_strict_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

(* Left translation on the strict category needs NO hypothesis: the arrow
   action is [f_equal], and both remaining functor laws close by destructing
   equality proofs.  There are only TWO obligations: the third field,
   [fmap_respects], is filled by instance resolution with
   [CMorphisms.reflexive_proper], the hom-setoid there being strict
   equality. *)
#[local] Obligation Tactic := idtac.

Program Definition LeftTranslationStrict (M : MonObject) (a : carrier M) :
  MonDiscreteStrict M ⟶ MonDiscreteStrict M := {|
  fobj := fun x => mon_op a x;
  fmap := fun x y (p : x = y) => f_equal (mon_op a) p
|}.
Next Obligation. intros M a x; reflexivity. Qed.
Next Obligation. intros M a x y z p q; now destruct p, q. Qed.

Section StrictAdjoint.
Context (M : MonObject) (HS : MonStrict M) (HU : MonUIP M).
Context (Inv : MonInverses M) (a : carrier M).

(* Where [MonStrict] is spent.  Within this section it occurs exactly twice,
   in the two definitions immediately below; everything after them goes
   through [strict_cancel_l]/[strict_cancel_r] and never mentions [HS].  It
   is spent once more elsewhere in the file, at [MonDiscreteToStrict] in
   Block G. *)
Definition strict_cancel_l (x : carrier M) :
  mon_op (minv Inv a) (mon_op a x) = x := HS _ _ (mon_inv_cancel_l M Inv a x).

Definition strict_cancel_r (y : carrier M) :
  mon_op a (mon_op (minv Inv a) y) = y := HS _ _ (mon_inv_cancel_l' M Inv a y).

Definition left_transpose_strict (x y : carrier M) (p : mon_op a x = y) :
  x = mon_op (minv Inv a) y :=
  eq_trans (eq_sym (strict_cancel_l x)) (f_equal (mon_op (minv Inv a)) p).

Definition left_untranspose_strict (x y : carrier M)
  (q : x = mon_op (minv Inv a) y) : mon_op a x = y :=
  eq_trans (f_equal (mon_op a) q) (strict_cancel_r y).

(* And this is where [MonUIP] is spent: every remaining field is an equation
   between two equality proofs. *)
#[local] Obligation Tactic := repeat intro; now apply HU.

Program Definition left_translation_strict_adjunction :
  LeftTranslationStrict M a ⊣ LeftTranslationStrict M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := left_transpose_strict x y |}
     ; from := {| morphism := left_untranspose_strict x y |} |}
|}.

End StrictAdjoint.

Definition LeftTranslationAdjointsStrict (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscreteStrict M ⟶ MonDiscreteStrict M &
      LeftTranslationStrict M a ⊣ R }.

(* The converse over the strict category needs NO hypothesis, because a
   Leibniz equality yields an `≈` outright.  The asymmetry with the forward
   direction is the whole content of the fork described in the header. *)
Definition strict_left_translation_adjoints_MonInverses (M : MonObject)
  (H : LeftTranslationAdjointsStrict M) : MonInverses M.
Proof.
  unshelve refine (MonInverses_of_right_inverses M
    (fun a => fobj[projT1 (H a)] mon_unit) _).
  intro a.
  refine (_ (from (@adj _ _ _ _ (projT2 (H a))
                     (fobj[projT1 (H a)] mon_unit) mon_unit) eq_refl)).
  intro e; simpl in e.
  now rewrite e.
Defined.

Theorem mon_group_iff_left_translation_adjoints_strict (M : MonObject)
  (HS : MonStrict M) (HU : MonUIP M) :
  MonInverses M ↔ LeftTranslationAdjointsStrict M.
Proof.
  split.
  - intros Inv a.
    exists (LeftTranslationStrict M (minv Inv a)).
    exact (left_translation_strict_adjunction M HS HU Inv a).
  - exact (strict_left_translation_adjoints_MonInverses M).
Defined.

(** ** Block G: comparing the two discrete categories *)

#[local] Obligation Tactic := repeat intro; exact I.

(* One way is free. *)
Program Definition MonStrictToDiscrete (M : MonObject) :
  MonDiscreteStrict M ⟶ MonDiscrete M := {|
  fobj := fun x => x;
  fmap := fun x y (p : x = y) =>
            match p with eq_refl => @id (MonDiscrete M) x end
|}.

Section Compare.
Context (M : MonObject) (HS : MonStrict M) (HU : MonUIP M).

(* The other costs exactly the two hypotheses: [MonStrict] for the arrow
   action, [MonUIP] for all three functor laws, each of which is an equation
   between equality proofs here.  (Three obligations, against two for
   [MonStrictToDiscrete], whose target is thin.) *)
#[local] Obligation Tactic := repeat intro; now apply HU.

Program Definition MonDiscreteToStrict :
  MonDiscrete M ⟶ MonDiscreteStrict M := {|
  fobj := fun x => x;
  fmap := fun x y f => HS x y f
|}.

End Compare.

Example mon_strict_to_discrete_obj (M : MonObject) (x : carrier M) :
  fobj[MonStrictToDiscrete M] x = x := eq_refl.

Example mon_discrete_to_strict_obj (M : MonObject) (HS : MonStrict M)
  (HU : MonUIP M) (x : carrier M) :
  fobj[MonDiscreteToStrict M HS HU] x = x := eq_refl.

(** ** Block H: witnesses *)

(* The discrete category on a monoid is not trivial: Z/3 gives two distinct
   objects with an EMPTY hom-set between them.  (This has to be checked at a
   concrete monoid: for a general M the hom x ~> y IS the type x ≈ y, which
   may perfectly well be inhabited for distinct x and y.) *)
Lemma Z3_two_objects : (Z3_0 : MonDiscrete Z3_Mon) <> Z3_1.
Proof. discriminate. Qed.

Lemma Z3_hom_empty : (Z3_0 ~{MonDiscrete Z3_Mon}~> Z3_1) → False.
Proof. intro p; discriminate. Qed.

(* (ℕ, +) is not a group, so by the biconditional its left translations
   cannot all have right adjoints.  The direct refutation is sharper: ONE
   translation suffices, and the contradiction is a computation.  From
   L_1 ⊣ R, the inverse transpose at the identity of R(0) reads
   1 + R(0) ≈ 0, that is S (R 0) = 0. *)
Lemma nat_translation_no_right_adjoint
  (R : MonDiscrete Nat_Plus ⟶ MonDiscrete Nat_Plus)
  (A : LeftTranslation Nat_Plus 1%nat ⊣ R) : False.
Proof.
  pose proof (from (@adj _ _ _ _ A (fobj[R] 0%nat) 0%nat) (reflexivity _))
    as e.
  simpl in e.
  discriminate.
Qed.

Corollary nat_no_right_adjoints : LeftTranslationAdjoints Nat_Plus → False.
Proof.
  intro H.
  exact (nat_plus_no_inverses
           (snd (mon_group_iff_left_translation_adjoints Nat_Plus) H)).
Qed.

(* The group witness.  Z/2 would be DEGENERATE here: every element is its own
   inverse ([bool_xor_self_adjoint]), so each left translation would be its
   own right adjoint and the adjunction would say nothing about inversion.
   Z/3 is the smallest group whose inversion moves an element
   (Structure/Groupoid.v's [Z3_inv_moves]), so over it the left adjoint and
   the right adjoint are provably different functors. *)
Definition Bool_Xor_Inverses : MonInverses Bool_Xor :=
  MonInverses_of Bool_Xor_Grp.

Example bool_xor_self_adjoint (b : carrier Bool_Xor) :
  minv Bool_Xor_Inverses b = b := eq_refl.

Definition Z3_Inverses : MonInverses Z3_Mon := MonInverses_of Z3_Grp.

Definition Z3_left_adjunction (a : carrier Z3_Mon) :
  LeftTranslation Z3_Mon a ⊣ LeftTranslation Z3_Mon (minv Z3_Inverses a) :=
  left_translation_adjunction Z3_Mon Z3_Inverses a.

Example Z3_left_adjoint_at :
  fobj[LeftTranslation Z3_Mon Z3_1] Z3_0 = Z3_1 := eq_refl.

Example Z3_right_adjoint_at :
  fobj[LeftTranslation Z3_Mon (minv Z3_Inverses Z3_1)] Z3_0 = Z3_2 := eq_refl.

Lemma Z3_adjoints_differ :
  fobj[LeftTranslation Z3_Mon Z3_1] Z3_0
    <> fobj[LeftTranslation Z3_Mon (minv Z3_Inverses Z3_1)] Z3_0.
Proof. discriminate. Qed.

(* Z/3's carrier setoid is Leibniz equality on [Z3] (Structure/Groupoid.v),
   so it also witnesses the strict reading, with both hypotheses discharged:
   [MonStrict] by the identity function, [MonUIP] by Hedberg. *)
Definition Z3_MonStrict : MonStrict Z3_Mon := fun _ _ p => p.

Definition Z3_dec (x y : Z3) : {x = y} + {x <> y}.
Proof.
  destruct x, y; solve [ left; reflexivity | right; discriminate ].
Defined.

Definition Z3_MonUIP : MonUIP Z3_Mon := MonUIP_dec Z3_Mon Z3_dec.

Definition Z3_strict_adjunction (a : carrier Z3_Mon) :
  LeftTranslationStrict Z3_Mon a
    ⊣ LeftTranslationStrict Z3_Mon (minv Z3_Inverses a) :=
  left_translation_strict_adjunction Z3_Mon Z3_MonStrict Z3_MonUIP
    Z3_Inverses a.

(** ** Block I: probes *)

(* FOUR negatives of TWO KINDS, plus a separate instrument check.  Each of
   the five was stripped of its [Fail] and compiled alone.
   [mon_probe_instrument], [probe_partial_record],
   [probe_categories_agree] and [probe_hom_is_eq] report `cannot unify`
   between two terms of one type (CONVERSION); [probe_cancel_strict] reports
   a plain type mismatch with NO `cannot unify` clause (TYPING).  Every
   negative is stated at a VARIABLE monoid, which matters for
   [probe_hom_is_eq]: at Z/3, whose `≈` IS `=`, that statement HOLDS, so a
   probe at a concrete monoid would have measured nothing.

   No constant a negative names, other than the negative's own name, is
   absent from a command that must SUCCEED (measured mechanically over the
   token sets, zero exceptions), so no guard here is vacuous. *)
Section Probes.
Context (M : MonObject) (Inv : MonInverses M) (a x y : carrier M).

(* Instrument check: [Fail] itself is doing something. *)
Fail Definition mon_probe_instrument : True = False := eq_refl.

Fail Definition probe_partial_record :
  LeftTranslation M a = Partial_r (MonMult M) a := eq_refl.

Fail Definition probe_categories_agree :
  MonDiscrete M = MonDiscreteStrict M := eq_refl.

Definition ctrl_objects_agree :
  obj[MonDiscrete M] = obj[MonDiscreteStrict M] := eq_refl.

Fail Definition probe_hom_is_eq :
  (x ~{MonDiscrete M}~> y) = (x = y) := eq_refl.

Definition ctrl_hom_is_equiv :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

Definition ctrl_strict_hom_is_eq :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

Fail Definition probe_cancel_strict :
  mon_op (minv Inv a) (mon_op a x) = x := mon_inv_cancel_l M Inv a x.

Definition ctrl_cancel_equiv :
  mon_op (minv Inv a) (mon_op a x) ≈ x := mon_inv_cancel_l M Inv a x.

End Probes.

(* The `Set` in the strict headline's constraint block sits on an internal
   universe — the auxiliary [Sets] in which [Adjunction] states its
   hom-isomorphism, whose carrier universe minimizes to `Set` because
   [DiscreteCat]'s homs are Rocq's `eq`, hence `Prop`-valued.  It does not
   restrict the monoid, and this section is the guard rather than a remark:
   all three of a monoid's universes are declared strictly above `Set` and
   both headlines still elaborate. *)
Section UniverseProbe.
Universe mo mh mp.
Constraint Set < mo.
Constraint Set < mh.
Constraint Set < mp.
Context (Mu : MonObject@{mo mh mp}).

Check (mon_group_iff_left_translation_adjoints Mu).
Check (mon_group_iff_left_translation_adjoints_strict Mu).
Check (MonDiscrete Mu).
Check (MonDiscreteStrict Mu).

End UniverseProbe.
