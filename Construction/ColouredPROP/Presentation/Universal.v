Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
(*
   本文件给出泛构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.
Require Import Category.Construction.ColouredPROP.Presentation.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * The 普遍性质 presented coloured PROP （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/generators+and+relations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CPresentedUniversal.

Context {Colour : Type}.
Context (E : CSMT Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (P : ColouredPROP Colour).
Context {HP : @HomEqProp P}.
Context {OD : @ObjDecEq P}.

Notation Σ := (csmt_sig E).

Context (v : CValuation P Σ).

Notation "⟦ cs ⟧" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧").

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CESound : Type :=
  ∀ (cs ds : list Colour) (s t : CTerm Σ cs ds),
    csmt_eqs E cs ds s t → cinterp P Σ v s ≈ cinterp P Σ v t.

Context (HE : CESound).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cinterpW_sound_heq {cs ds : list Colour} {s t : CTerm Σ cs ds} :
  CTermEqW E s t → heq (cinterp P Σ v s) (cinterp P Σ v t).
Proof using E HE HP OD P v.
  intros HT.
  induction HT as
    [ cs ds s t Hst
    | cs ds s t Hax
    | cs ds s t Hst IH
    | cs ds s t u Hst IH1 Htu IH2
    | cs ds es f f' g g' Hf IHf Hg IHg
    | cs1 ds1 cs2 ds2 f f' g g' Hf IHf Hg IHg ].
  - (* CTEW_termeq: a free equation *)
    exact (cinterp_sound_heq P Σ v Hst).
  - (* CTEW_ax: an axiom of the theory *)
    exact (heq_intro (HE _ _ s t Hax)).
  - (* CTEW_sym *)
    apply heq_intro; symmetry; exact (heq_elim IH).
  - (* CTEW_trans *)
    apply heq_intro.
    rewrite (heq_elim IH1).
    exact (heq_elim IH2).
  - (* CTEW_comp *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
  - (* CTEW_tens *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
Qed.

(** Soundness, in the target's own hom equivalence. *)
Theorem cinterpW_sound {cs ds : list Colour} {s t : CTerm Σ cs ds} :
  CTermEqW E s t → cinterp P Σ v s ≈ cinterp P Σ v t.
Proof using E HE HP OD P v.
  intros HT.
  exact (heq_elim (cinterpW_sound_heq HT)).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CPresentedInterp : CPresentedCat E ⟶ P :=
  @QuotientLift (CFreeCat Σ)
    (fun cs ds : list Colour => @CTermEqW Colour E cs ds)
    (CTermEqW_Congruence E) P (CInterpF Σ P v)
    (fun (cs ds : list Colour) (s t : CTerm Σ cs ds)
         (H : CTermEqW E s t) => cinterpW_sound H).

(** 本节：The factorisation through projection DEFINITIONAL: both
 sides very same interpretation very same term. （已译） *)
Lemma CPresentedInterp_proj {cs ds : list Colour} (t : CTerm Σ cs ds) :
  fmap[CPresentedInterp] (fmap[CPresentedProj E] t)
  = fmap[CInterpF Σ P v] t.
Proof. reflexivity. Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CPresentedInterp_ap_dom :
  CPresentedCat E ∏ CPresentedCat E ⟶ P :=
  @tensor P (MPc P) ◯ CPresentedInterp ∏⟶ CPresentedInterp.

Definition CPresentedInterp_ap_cod :
  CPresentedCat E ∏ CPresentedCat E ⟶ P :=
  CPresentedInterp ◯ @tensor (CPresentedCat E) (CPresented_Monoidal E Cdec).

Definition CPresentedInterp_ap_to :
  CPresentedInterp_ap_dom ⟹ CPresentedInterp_ap_cod :=
  @Build_Transform' (CPresentedCat E ∏ CPresentedCat E) P
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod
    (fun mn => id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    (fun x y f => cinterp_ap_natural Σ P v (fst f) (snd f)).

Definition CPresentedInterp_ap_from :
  CPresentedInterp_ap_cod ⟹ CPresentedInterp_ap_dom :=
  @Build_Transform' (CPresentedCat E ∏ CPresentedCat E) P
    CPresentedInterp_ap_cod CPresentedInterp_ap_dom
    (fun mn =>
       id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn))))
    (fun x y f => cinterp_ap_natural_from Σ P v (fst f) (snd f)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CPresentedInterp_ap_to_from
  (mn : CPresentedCat E ∏ CPresentedCat E) :
  id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
      ∘ id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    ≈ cinterp P Σ v (CT_tens (CT_id (fst mn)) (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [cinterp].
  apply ctensor_hom_id.
Qed.

Lemma CPresentedInterp_ap_from_to
  (mn : CPresentedCat E ∏ CPresentedCat E) :
  id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
      ∘ id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
    ≈ (cinterp P Σ v (CT_id (fst mn))
         ⨂[MPc P] cinterp P Σ v (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [cinterp].
  apply bimap_id_id.
Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CPresentedInterp_ap_iso :
  @Isomorphism
    (@Category.Instance.Fun.Fun (CPresentedCat E ∏ CPresentedCat E) P)
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod :=
  @Build_Isomorphism
    (@Category.Instance.Fun.Fun (CPresentedCat E ∏ CPresentedCat E) P)
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod
    CPresentedInterp_ap_to CPresentedInterp_ap_from
    CPresentedInterp_ap_to_from CPresentedInterp_ap_from_to.

(** The strong monoidal structure. All data fields casts all
 证明 fields named lemmas [Universal.v] §2. （已译） *)
Definition CPresentedInterp_Monoidal :
  @MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp :=
  @Build_MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp
    (id_cast_iso (@cprop_unit_nil Colour P))
    CPresentedInterp_ap_iso
    (fun x : list Colour => @unit_left P (MPc P) ⟦x⟧)
    (fun x : list Colour =>
       iso_compose
         (id_cast_iso (f_equal (@cprop_of_list Colour P)
                               (eq_sym (app_nil_r x))))
         (@unit_right P (MPc P) ⟦x⟧))
    (fun x y z : list Colour =>
       id_cast_iso
         (eq_trans
            (f_equal (fun u : P => (u ⨂[MPc P] ⟦z⟧)%object)
                     (@cprop_tensor_app Colour P x y))
            (eq_trans (@cprop_tensor_app Colour P (x ++ y) z)
                      (f_equal (@cprop_of_list Colour P)
                               (eq_sym (app_assoc x y z))))))
    (fun x : list Colour => cinterp_monoidal_unit_left Σ P v x)
    (fun x : list Colour => cinterp_monoidal_unit_right Σ P v x)
    (fun x y z : list Colour => cinterp_monoidal_assoc Σ P v x y z).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CPresentedInterp_Strict :
  @StrictMonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp := {|
  strict_functor_is_monoidal := CPresentedInterp_Monoidal;
  strict_pure_obj := @cprop_unit_nil Colour P;         (* the class field *)
  strict_ap_obj := fun x y : list Colour =>
    @cprop_tensor_app Colour P x y                     (* ditto *)
|}.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CSymmetricStrictW (G : CPresentedCat E ⟶ P)
  (MG : @MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
          (MPc P) G) : Type :=
  ∀ cs ds : list Colour,
    fmap[G] (cquot E (CT_braid cs ds)) ∘ to (@ap_iso _ _ _ _ G MG cs ds)
      ≈ to (@ap_iso _ _ _ _ G MG ds cs) ∘ cstrict_braid P (G cs) (G ds).

Lemma CPresentedInterp_SymmetricStrict :
  CSymmetricStrictW CPresentedInterp CPresentedInterp_Monoidal.
Proof.
  intros cs ds.
  exact (cinterp_braid_ap Σ P v cs ds).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem CPresented_factor : ∀ cs ds (t : CTerm Σ cs ds),
  fmap[CPresentedInterp] (fmap[CPresentedProj E] t) ≈ cinterp P Σ v t.
Proof.
  intros; reflexivity.
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CPresentedUniqueness.

Context (G : CPresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (CPresentedCat E) P
                (CPresented_Monoidal E Cdec) (MPc P) G).
Context (HBW : CSymmetricStrictW G SG).
Context (Hobj : ∀ cs : list Colour, G cs = ⟦cs⟧).
Context (Hgen : ∀ cs ds (g : Σ cs ds),
  fmap[G] (cquot E (CT_gen g))
    ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds)) (v cs ds g)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CPresentedComposite : CFreeCat Σ ⟶ P := G ◯ CPresentedProj E.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CPresentedComposite_Strict :
  @StrictMonoidalFunctor (CFreeCat Σ) P (CFreeCat_Monoidal Σ Cdec)
    (MPc P) CPresentedComposite :=
  @Compose_StrictMonoidalFunctor (CFreeCat Σ) (CPresentedCat E) P
    (CFreeCat_Monoidal Σ Cdec) (CPresented_Monoidal E Cdec) (MPc P)
    G (CPresentedProj E) SG (CPresentedProj_Strict E Cdec).

(** Machine-checked: 复合's strict 对象 comparisons ARE
 [SG]'s, definitionally. This cast-fusing content the
 precomposition route. （已译） *)
Example CPresentedComposite_ap_obj_is_SG (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CPresentedComposite CPresentedComposite_Strict x y
  = @strict_ap_obj _ _ _ _ G SG x y := eq_refl.

Example CPresentedComposite_pure_obj_is_SG :
  @strict_pure_obj _ _ _ _ CPresentedComposite CPresentedComposite_Strict
  = @strict_pure_obj _ _ _ _ G SG := eq_refl.

(** Both tensor comparisons, spelled cast along [SG]'s 对象
 equality (复合's comparison converts same cast,
 [Example]s above). （已译） *)
Lemma CPresentedComposite_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ CPresentedComposite
        (@strict_functor_is_monoidal _ _ _ _ CPresentedComposite
           CPresentedComposite_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ CPresentedComposite
           CPresentedComposite_Strict x y).
Qed.

Lemma CPresented_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ G SG x y).
Qed.

(** The 复合 inherits braid-compatibility square [HBW]:
 rewriting all four comparisons SAME cast aligns two
 squares, remaining sides agree definitionally. （已译） *)
Lemma CPresentedComposite_SymmetricStrict :
  CSymmetricStrict Σ Cdec P CPresentedComposite
    (@strict_functor_is_monoidal _ _ _ _ CPresentedComposite
       CPresentedComposite_Strict).
Proof using Cdec E G HBW P SG.
  intros x y.
  rewrite (CPresentedComposite_ap_cast x y).
  rewrite (CPresentedComposite_ap_cast y x).
  pose proof (HBW x y) as HB.
  rewrite (CPresented_ap_cast x y) in HB.
  rewrite (CPresented_ap_cast y x) in HB.
  exact HB.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem CPresented_unique :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    fmap[G] f ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds))
                         (cinterp P Σ v f).
Proof using Cdec E G HBW Hgen Hobj OD P SG v.
  intros cs ds f.
  exact (cinterp_unique Σ Cdec P v CPresentedComposite
           CPresentedComposite_Strict CPresentedComposite_SymmetricStrict
           Hobj Hgen cs ds f).
Qed.

End CPresentedUniqueness.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example CPresentedInterp_generator_agreement (cs ds : list Colour)
  (g : Σ cs ds) :
  fmap[CPresentedInterp] (cquot E (CT_gen g))
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦cs⟧)) (eq_sym (@eq_refl _ ⟦ds⟧))
               (v cs ds g).
Proof. reflexivity. Qed.

Example CPresentedInterp_unique_self (cs ds : list Colour)
  (f : cs ~{CPresentedCat E}~> ds) :
  fmap[CPresentedInterp] f
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦cs⟧)) (eq_sym (@eq_refl _ ⟦ds⟧))
               (cinterp P Σ v f).
Proof using Cdec E HE HP OD P v.
  exact (CPresented_unique CPresentedInterp CPresentedInterp_Strict
           CPresentedInterp_SymmetricStrict (fun ks : list Colour => eq_refl)
           CPresentedInterp_generator_agreement cs ds f).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CPresentedUniquenessFromWires.

Context (G : CPresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (CPresentedCat E) P
                (CPresented_Monoidal E Cdec) (MPc P) G).
Context (HBW : CSymmetricStrictW G SG).
Context (H1 : ∀ c : Colour, G [c] = ⟦[c]⟧).

Fixpoint CPresentedG_obj (cs : list Colour) : G cs = ⟦cs⟧ :=
  match cs with
  | [] => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                   (@cprop_unit_nil Colour P)
  | c :: cs' =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG [c] cs'))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MPc P] b)%object)
                     (H1 c) (CPresentedG_obj cs'))
           (@cprop_tensor_app Colour P [c] cs'))
  end.

Corollary CPresented_unique_from_wires
  (Hgen : ∀ cs ds (g : Σ cs ds),
     fmap[G] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (CPresentedG_obj cs))
                  (eq_sym (CPresentedG_obj ds)) (v cs ds g)) :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    fmap[G] f ≈ hom_cast (eq_sym (CPresentedG_obj cs))
                         (eq_sym (CPresentedG_obj ds))
                         (cinterp P Σ v f).
Proof using Cdec E G H1 HBW OD P SG v.
  exact (CPresented_unique G SG HBW CPresentedG_obj Hgen).
Qed.

End CPresentedUniquenessFromWires.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary CPresented_unique2
  (G1 : CPresentedCat E ⟶ P)
  (SG1 : @StrictMonoidalFunctor (CPresentedCat E) P
           (CPresented_Monoidal E Cdec) (MPc P) G1)
  (HBW1 : CSymmetricStrictW G1 SG1)
  (Hobj1 : ∀ cs : list Colour, G1 cs = ⟦cs⟧)
  (Hgen1 : ∀ cs ds (g : Σ cs ds),
     fmap[G1] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (Hobj1 cs)) (eq_sym (Hobj1 ds)) (v cs ds g))
  (G2 : CPresentedCat E ⟶ P)
  (SG2 : @StrictMonoidalFunctor (CPresentedCat E) P
           (CPresented_Monoidal E Cdec) (MPc P) G2)
  (HBW2 : CSymmetricStrictW G2 SG2)
  (Hobj2 : ∀ cs : list Colour, G2 cs = ⟦cs⟧)
  (Hgen2 : ∀ cs ds (g : Σ cs ds),
     fmap[G2] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (Hobj2 cs)) (eq_sym (Hobj2 ds)) (v cs ds g)) :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    hom_cast (Hobj1 cs) (Hobj1 ds) (fmap[G1] f)
      ≈ hom_cast (Hobj2 cs) (Hobj2 ds) (fmap[G2] f).
Proof using Cdec E OD P v.
  intros cs ds f.
  rewrite (CPresented_unique G1 SG1 HBW1 Hobj1 Hgen1 cs ds f).
  rewrite (CPresented_unique G2 SG2 HBW2 Hobj2 Hgen2 cs ds f).
  now rewrite !hom_cast_roundtrip.
Qed.

(* 相关说明。 （已译） *)

(** The lifted 函子 acts interpretation terms. （已译） *)
Example CPresentedInterp_fmap_on_terms {cs ds : list Colour}
  (t : CTerm Σ cs ds) :
  fmap[CPresentedInterp] (cquot E t) = cinterp P Σ v t := eq_refl.

(** The strict 对象 comparisons [CPresentedInterp_Strict] the
 coloured-PROP class fields themselves. （已译） *)
Example CPresentedInterp_strict_pure_obj_is_cprop_unit_nil :
  @strict_pure_obj _ _ _ _ CPresentedInterp CPresentedInterp_Strict
  = @cprop_unit_nil Colour P := eq_refl.

Example CPresentedInterp_strict_ap_obj_is_cprop_tensor_app
  (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CPresentedInterp CPresentedInterp_Strict x y
  = @cprop_tensor_app Colour P x y := eq_refl.

(** 本节：Every axiom theory holds under lifted interpretation —
 end-to-end form [CESound]. （已译） *)
Example CPresentedInterp_respects_axioms {cs ds : list Colour}
  (s t : CTerm Σ cs ds) (Hax : csmt_eqs E cs ds s t) :
  fmap[CPresentedInterp] (cquot E s) ≈ fmap[CPresentedInterp] (cquot E t) :=
  cinterpW_sound (CTEW_ax E s t Hax).

End CPresentedUniversal.

Arguments CESound {Colour} E P v : assert.
Arguments CPresentedInterp {Colour} E P {HP OD} v HE : assert.
Arguments CSymmetricStrictW {Colour} E Cdec P G MG : assert.
