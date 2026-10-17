Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Construction.PROP.Presentation.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The universal property of a presented PROP *)

(*
   nLab: https://ncatlab.org/nlab/show/generators+and+relations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

   本文件给出泛构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PresentedUniversal.

Context (E : SMT).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.

Notation Σ := (smt_sig E).

Context (v : Valuation P Σ).

Open Scope nat_scope.

Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ESound : Type :=
  ∀ m n (s t : Term Σ m n),
    smt_eqs E m n s t → interp P Σ v s ≈ interp P Σ v t.

Context (Hv : ESound).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma interpW_sound_heq {m n : nat} {s t : Term Σ m n} :
  TermEqW E s t → heq (interp P Σ v s) (interp P Σ v t).
Proof using E HP Hv OD P v.
  intros HT.
  induction HT as
    [ m n s t Hst
    | m n s t Hax
    | m n s t Hst IH
    | m n s t u Hst IH1 Htu IH2
    | m n p f f' g g' Hf IHf Hg IHg
    | m1 n1 m2 n2 f f' g g' Hf IHf Hg IHg ].
  - (* TEW_termeq: a free equation *)
    exact (interp_sound_heq P Σ v Hst).
  - (* TEW_ax: an axiom of the theory *)
    exact (heq_intro (Hv _ _ s t Hax)).
  - (* TEW_sym *)
    apply heq_intro; symmetry; exact (heq_elim IH).
  - (* TEW_trans *)
    apply heq_intro.
    rewrite (heq_elim IH1).
    exact (heq_elim IH2).
  - (* TEW_comp *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
  - (* TEW_tens *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
Qed.

(** Soundness, in the target's own hom equivalence. *)
Theorem interpW_sound {m n : nat} {s t : Term Σ m n} :
  TermEqW E s t → interp P Σ v s ≈ interp P Σ v t.
Proof using E HP Hv OD P v.
  intros HT.
  exact (heq_elim (interpW_sound_heq HT)).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PresentedInterp : PresentedCat E ⟶ P :=
  @QuotientLift (FreeCat Σ) (fun m n : nat => @TermEqW E m n)
    (TermEqW_Congruence E) P (InterpF Σ P v)
    (fun (m n : nat) (s t : Term Σ m n) (H : TermEqW E s t) =>
       interpW_sound H).

(** The factorisation through the projection is DEFINITIONAL: both
    sides are the very same interpretation of the very same term. *)
Lemma PresentedInterp_proj {m n : nat} (t : Term Σ m n) :
  fmap[PresentedInterp] (fmap[PresentedProj E] t) = fmap[InterpF Σ P v] t.
Proof. reflexivity. Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PresentedInterp_ap_dom :
  PresentedCat E ∏ PresentedCat E ⟶ P :=
  @tensor P (MP P) ◯ PresentedInterp ∏⟶ PresentedInterp.

Definition PresentedInterp_ap_cod :
  PresentedCat E ∏ PresentedCat E ⟶ P :=
  PresentedInterp ◯ @tensor (PresentedCat E) (Presented_Monoidal E).

Definition PresentedInterp_ap_to :
  PresentedInterp_ap_dom ⟹ PresentedInterp_ap_cod :=
  @Build_Transform' (PresentedCat E ∏ PresentedCat E) P
    PresentedInterp_ap_dom PresentedInterp_ap_cod
    (fun mn => id_cast (prop_tensor_plus (fst mn) (snd mn)))
    (fun x y f => interp_ap_natural Σ P v (fst f) (snd f)).

Definition PresentedInterp_ap_from :
  PresentedInterp_ap_cod ⟹ PresentedInterp_ap_dom :=
  @Build_Transform' (PresentedCat E ∏ PresentedCat E) P
    PresentedInterp_ap_cod PresentedInterp_ap_dom
    (fun mn => id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn))))
    (fun x y f => interp_ap_natural_from Σ P v (fst f) (snd f)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PresentedInterp_ap_to_from (mn : PresentedCat E ∏ PresentedCat E) :
  id_cast (prop_tensor_plus (fst mn) (snd mn))
      ∘ id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
    ≈ interp P Σ v (T_tens (T_id (fst mn)) (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [interp].
  apply tensor_hom_id.
Qed.

Lemma PresentedInterp_ap_from_to (mn : PresentedCat E ∏ PresentedCat E) :
  id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
      ∘ id_cast (prop_tensor_plus (fst mn) (snd mn))
    ≈ (interp P Σ v (T_id (fst mn)) ⨂[MP P] interp P Σ v (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [interp].
  apply bimap_id_id.
Qed.

Program Definition PresentedInterp_ap_iso :
  PresentedInterp_ap_dom
    ≅[[PresentedCat E ∏ PresentedCat E, P]] PresentedInterp_ap_cod := {|
  to := PresentedInterp_ap_to;
  from := PresentedInterp_ap_from;
  iso_to_from := PresentedInterp_ap_to_from;
  iso_from_to := PresentedInterp_ap_from_to
|}.

(** The strong monoidal structure.  All data fields are casts and all
    proof fields are the named lemmas of [Universal.v] §2. *)
Program Definition PresentedInterp_Monoidal :
  @MonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P)
    PresentedInterp := {|
  pure_iso := id_cast_iso (@prop_unit_zero P);
  ap_functor_iso := PresentedInterp_ap_iso;
  pure_iso_left := fun x : nat => @unit_left P (MP P) ⟦x⟧;
  pure_iso_right := fun x : nat =>
    iso_compose
      (id_cast_iso (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r x))))
      (@unit_right P (MP P) ⟦x⟧);
  ap_iso_assoc := fun x y z : nat =>
    id_cast_iso
      (eq_trans
         (f_equal (fun u : P => (u ⨂[MP P] ⟦z⟧)%object)
                  (prop_tensor_plus x y))
         (eq_trans (prop_tensor_plus (x + y) z)
                   (f_equal (@prop_of_nat P)
                            (eq_sym (Nat.add_assoc x y z)))));
  monoidal_unit_left := interp_monoidal_unit_left Σ P v;
  monoidal_unit_right := interp_monoidal_unit_right Σ P v;
  monoidal_assoc := interp_monoidal_assoc Σ P v
|}.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition PresentedInterp_Strict :
  @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P)
    PresentedInterp := {|
  strict_functor_is_monoidal := PresentedInterp_Monoidal;
  strict_pure_obj := @prop_unit_zero P;               (* the PROP field *)
  strict_ap_obj := fun x y : nat => @prop_tensor_plus P x y      (* ditto *)
|}.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SymmetricStrictW (G : PresentedCat E ⟶ P)
  (MG : @MonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P) G) :
  Type :=
  ∀ m n : nat,
    fmap[G] (quot E (T_braid m n)) ∘ to (@ap_iso _ _ _ _ G MG m n)
      ≈ to (@ap_iso _ _ _ _ G MG n m) ∘ strict_braid P (G m) (G n).

Lemma PresentedInterp_SymmetricStrict :
  SymmetricStrictW PresentedInterp PresentedInterp_Monoidal.
Proof.
  intros m n.
  exact (interp_braid_ap Σ P v m n).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Presented_factor : ∀ m n (t : Term Σ m n),
  fmap[PresentedInterp] (fmap[PresentedProj E] t) ≈ interp P Σ v t.
Proof.
  intros; reflexivity.
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PresentedUniqueness.

Context (G : PresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (PresentedCat E) P
                (Presented_Monoidal E) (MP P) G).
Context (HBW : SymmetricStrictW G SG).
Context (Hobj : ∀ n : nat, G n = ⟦n⟧).
Context (Hgen : ∀ m n (g : Σ m n),
  fmap[G] (quot E (T_gen g))
    ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (v m n g)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PresentedComposite : FreeCat Σ ⟶ P := G ◯ PresentedProj E.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PresentedComposite_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) P (FreeCat_Monoidal Σ) (MP P)
    PresentedComposite :=
  @Compose_StrictMonoidalFunctor (FreeCat Σ) (PresentedCat E) P
    (FreeCat_Monoidal Σ) (Presented_Monoidal E) (MP P)
    G (PresentedProj E) SG (PresentedProj_Strict E).

(** Machine-checked: the composite's strict object comparisons ARE
    [SG]'s, definitionally.  This is the cast-fusing content of the
    precomposition route. *)
Example PresentedComposite_ap_obj_is_SG (x y : nat) :
  @strict_ap_obj _ _ _ _ PresentedComposite PresentedComposite_Strict x y
  = @strict_ap_obj _ _ _ _ G SG x y := eq_refl.

Example PresentedComposite_pure_obj_is_SG :
  @strict_pure_obj _ _ _ _ PresentedComposite PresentedComposite_Strict
  = @strict_pure_obj _ _ _ _ G SG := eq_refl.

(** Both tensor comparisons, spelled as the cast along [SG]'s object
    equality (the composite's comparison converts to the same cast,
    by the [Example]s above). *)
Lemma PresentedComposite_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ PresentedComposite
        (@strict_functor_is_monoidal _ _ _ _ PresentedComposite
           PresentedComposite_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ PresentedComposite
           PresentedComposite_Strict x y).
Qed.

Lemma Presented_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ G SG x y).
Qed.

(** The composite inherits the braid-compatibility square from [HBW]:
    rewriting all four comparisons to the SAME cast aligns the two
    squares, and the remaining sides agree definitionally. *)
Lemma PresentedComposite_SymmetricStrict :
  SymmetricStrict Σ P PresentedComposite
    (@strict_functor_is_monoidal _ _ _ _ PresentedComposite
       PresentedComposite_Strict).
Proof using E G HBW P SG.
  intros x y.
  rewrite (PresentedComposite_ap_cast x y).
  rewrite (PresentedComposite_ap_cast y x).
  pose proof (HBW x y) as HB.
  rewrite (Presented_ap_cast x y) in HB.
  rewrite (Presented_ap_cast y x) in HB.
  exact HB.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Presented_unique :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    fmap[G] f ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n))
                         (interp P Σ v f).
Proof using E G HBW Hgen Hobj OD P SG v.
  intros m n f.
  exact (interp_unique Σ P v PresentedComposite PresentedComposite_Strict
           PresentedComposite_SymmetricStrict Hobj Hgen m n f).
Qed.

End PresentedUniqueness.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example PresentedInterp_generator_agreement (m n : nat) (g : Σ m n) :
  fmap[PresentedInterp] (quot E (T_gen g))
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (v m n g).
Proof. reflexivity. Qed.

Example PresentedInterp_unique_self (m n : nat)
  (f : m ~{PresentedCat E}~> n) :
  fmap[PresentedInterp] f
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (interp P Σ v f).
Proof.
  exact (Presented_unique PresentedInterp PresentedInterp_Strict
           PresentedInterp_SymmetricStrict (fun k : nat => eq_refl)
           PresentedInterp_generator_agreement m n f).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PresentedUniquenessFromOne.

Context (G : PresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (PresentedCat E) P
                (Presented_Monoidal E) (MP P) G).
Context (HBW : SymmetricStrictW G SG).
Context (H1 : G 1 = ⟦1⟧).

Fixpoint PresentedG_obj (n : nat) : G n = ⟦n⟧ :=
  match n with
  | O => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                  (@prop_unit_zero P)
  | Datatypes.S k =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG 1 k))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MP P] b)%object) H1
                     (PresentedG_obj k))
           (@prop_tensor_plus P 1 k))
  end.

Corollary Presented_unique_from_one
  (Hgen : ∀ m n (g : Σ m n),
     fmap[G] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (PresentedG_obj m)) (eq_sym (PresentedG_obj n))
                  (v m n g)) :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    fmap[G] f ≈ hom_cast (eq_sym (PresentedG_obj m))
                         (eq_sym (PresentedG_obj n))
                         (interp P Σ v f).
Proof using E G H1 HBW OD P SG v.
  exact (Presented_unique G SG HBW PresentedG_obj Hgen).
Qed.

End PresentedUniquenessFromOne.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary Presented_unique2
  (G1 : PresentedCat E ⟶ P)
  (SG1 : @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E)
           (MP P) G1)
  (HBW1 : SymmetricStrictW G1 SG1)
  (Hobj1 : ∀ n : nat, G1 n = ⟦n⟧)
  (Hgen1 : ∀ m n (g : Σ m n),
     fmap[G1] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (Hobj1 m)) (eq_sym (Hobj1 n)) (v m n g))
  (G2 : PresentedCat E ⟶ P)
  (SG2 : @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E)
           (MP P) G2)
  (HBW2 : SymmetricStrictW G2 SG2)
  (Hobj2 : ∀ n : nat, G2 n = ⟦n⟧)
  (Hgen2 : ∀ m n (g : Σ m n),
     fmap[G2] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (Hobj2 m)) (eq_sym (Hobj2 n)) (v m n g)) :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    hom_cast (Hobj1 m) (Hobj1 n) (fmap[G1] f)
      ≈ hom_cast (Hobj2 m) (Hobj2 n) (fmap[G2] f).
Proof using E OD P v.
  intros m n f.
  rewrite (Presented_unique G1 SG1 HBW1 Hobj1 Hgen1 m n f).
  rewrite (Presented_unique G2 SG2 HBW2 Hobj2 Hgen2 m n f).
  now rewrite !hom_cast_roundtrip.
Qed.

(** ** Machine-checked sanity

    Each [Example] pins a definitional behaviour, so any regression in
    the quotient-lifting or shared-record wiring is caught here rather
    than at a distant use site. *)

(** The lifted functor acts as the interpretation on terms. *)
Example PresentedInterp_fmap_on_terms {m n : nat} (t : Term Σ m n) :
  fmap[PresentedInterp] (quot E t) = interp P Σ v t := eq_refl.

(** The strict object comparisons of [PresentedInterp_Strict] are the
    PROP class fields themselves. *)
Example PresentedInterp_strict_pure_obj_is_prop_unit_zero :
  @strict_pure_obj _ _ _ _ PresentedInterp PresentedInterp_Strict
  = @prop_unit_zero P := eq_refl.

Example PresentedInterp_strict_ap_obj_is_prop_tensor_plus (x y : nat) :
  @strict_ap_obj _ _ _ _ PresentedInterp PresentedInterp_Strict x y
  = @prop_tensor_plus P x y := eq_refl.

(** Every axiom of the theory holds under the lifted interpretation —
    the end-to-end form of [ESound]. *)
Example PresentedInterp_respects_axioms {m n : nat} (s t : Term Σ m n)
  (Hax : smt_eqs E m n s t) :
  fmap[PresentedInterp] (quot E s) ≈ fmap[PresentedInterp] (quot E t) :=
  interpW_sound (TEW_ax E s t Hax).

End PresentedUniversal.

Arguments ESound E P v : assert.
Arguments PresentedInterp E P {HP OD} v Hv : assert.
Arguments SymmetricStrictW E P G MG : assert.
