(* * * Translation endofunctors 幺半群, adjoints （已译） *)

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

(* * ** Block A: discrete 范畴 幺半群 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition MonDiscrete (M : MonObject) : Category :=
  DiscreteSetoidCat (@is_setoid (mon_setoid M)).

Example mon_discrete_obj (M : MonObject) :
  obj[MonDiscrete M] = carrier M := eq_refl.

Example mon_discrete_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma MonDiscrete_thin (M : MonObject) (x y : MonDiscrete M)
  (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(* 相关说明。 （已译） *)

#[local] Obligation Tactic := repeat intro; exact I.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 Translation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* 相关说明。 （已译） *)

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

(* 相关说明。 （已译） *)

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

(* Every remaining field [Adjunction] — both 同构 laws, both
 respectfulness 证明 all four 自然性 clauses — is equation in
 hom-setoid [MonDiscrete M], hence trivially true; obligation
 tactic force discharges all eight.（已译） *)
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

(* 相关说明。 （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* The 镜像, right translations: all left inverses gives group. （已译） *)
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

(* "Every left translation has 右伴随", DATA. The library's ∃ is
 [sigT], so 这是 function no choice principle consumed the
 inverse operation read off it. （已译） *)
Definition LeftTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & LeftTranslation M a ⊣ R }.

Definition RightTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & RightTranslation M a ⊣ R }.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition MonStrict (M : MonObject) : Type :=
  ∀ x y : carrier M, x ≈ y → x = y.

Definition MonUIP (M : MonObject) : Type :=
  ∀ (x y : carrier M) (p q : x = y), p = q.

(* Hedberg, via the stdlib's axiom-free [UIP_dec]. *)
Definition MonUIP_dec (M : MonObject)
  (dec : ∀ x y : carrier M, {x = y} + {x <> y}) : MonUIP M := UIP_dec dec.

(* The explicit binders load-bearing: unannotated, body minimizes so
 identify hom 证明 universes result. （已译） *)
Definition MonDiscreteStrict@{o h p m1 m2} (M : MonObject@{o m1 m2}) :
  Category@{o h p} := DiscreteCat@{o h p} (carrier M).

Example mon_discrete_strict_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* And 这是 where [MonUIP] spent: every remaining field equation
 between two equality proofs. （已译） *)
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

(*
   本节说明 Translation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* * ** Block G: comparing two discrete 范畴 （已译） *)

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

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Z3_two_objects : (Z3_0 : MonDiscrete Z3_Mon) <> Z3_1.
Proof. discriminate. Qed.

Lemma Z3_hom_empty : (Z3_0 ~{MonDiscrete Z3_Mon}~> Z3_1) → False.
Proof. intro p; discriminate. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* Z/3's carrier setoid is Leibniz equality [Z3] (Structure/Groupoid.v),
 so it also witnesses 严格 reading, both hypotheses discharged:
 [MonStrict] 恒等 function, [MonUIP] Hedberg.（已译） *)
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

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明伴随、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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
