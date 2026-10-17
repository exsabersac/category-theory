Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
(*
   本文件给出构造。

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

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Presentations of coloured PROPs by many-sorted symmetric monoidal
      theories *)

(*
   nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/generators+and+relations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Coloured symmetric monoidal theories *)

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CEqSystem {Colour : Type} (S : CSignature Colour) : Type :=
  ∀ cs ds : list Colour, CTerm S cs ds → CTerm S cs ds → Prop.

(** A coloured symmetric monoidal theory: generators plus equations. *)
Record CSMT (Colour : Type) : Type := {
  csmt_sig : CSignature Colour;
  csmt_eqs : CEqSystem csmt_sig
}.

Arguments csmt_sig {Colour} _.
Arguments csmt_eqs {Colour} _ cs ds _ _.

Section Presented.

Context {Colour : Type}.
Context (E : CSMT Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

Notation Σ := (csmt_sig E).

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive CTermEqW : forall {cs ds}, CTerm Σ cs ds → CTerm Σ cs ds → Prop :=

  (** Every free equation holds in the presented coloured PROP. *)
  | CTEW_termeq {cs ds} (s t : CTerm Σ cs ds) :
      CTermEq Σ s t → CTermEqW s t

  (** Every axiom of the theory holds in the presented coloured PROP. *)
  | CTEW_ax {cs ds} (s t : CTerm Σ cs ds) :
      csmt_eqs E cs ds s t → CTermEqW s t

  (** Closure under symmetry and transitivity. *)
  | CTEW_sym {cs ds} (s t : CTerm Σ cs ds) :
      CTermEqW s t → CTermEqW t s
  | CTEW_trans {cs ds} (s t u : CTerm Σ cs ds) :
      CTermEqW s t → CTermEqW t u → CTermEqW s u

  (** Closure under the two composition operations. *)
  | CTEW_comp {cs ds es} (f f' : CTerm Σ ds es) (g g' : CTerm Σ cs ds) :
      CTermEqW f f' → CTermEqW g g' →
      CTermEqW (CT_comp f g) (CT_comp f' g')
  | CTEW_tens {cs1 ds1 cs2 ds2}
      (f f' : CTerm Σ cs1 ds1) (g g' : CTerm Σ cs2 ds2) :
      CTermEqW f f' → CTermEqW g g' →
      CTermEqW (CT_tens f g) (CT_tens f' g').

(** Reflexivity of the theory congruence, via the embedding. *)
Definition CTermEqW_refl {cs ds : list Colour} (t : CTerm Σ cs ds) :
  CTermEqW t t :=
  CTEW_termeq t t (CTE_refl t).

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance CTermEqW_Congruence :
  @HomCongruence (CFreeCat Σ) (fun cs ds : list Colour => @CTermEqW cs ds) :=
  @Build_HomCongruence (CFreeCat Σ)
    (fun cs ds : list Colour => @CTermEqW cs ds)
    (fun (cs ds : list Colour) (s t : CTerm Σ cs ds) H =>
       CTEW_termeq s t H)
    (fun (cs ds : list Colour) (s t : CTerm Σ cs ds) H =>
       CTEW_sym s t H)
    (fun (cs ds : list Colour) (s t u : CTerm Σ cs ds) H1 H2 =>
       CTEW_trans s t u H1 H2)
    (fun (cs ds es : list Colour)
         (f f' : CTerm Σ ds es) (g g' : CTerm Σ cs ds) Hf Hg =>
       CTEW_comp f f' g g' Hf Hg).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CPresentedCat : Category :=
  @Quotient (CFreeCat Σ) (fun cs ds : list Colour => @CTermEqW cs ds)
    CTermEqW_Congruence.

(** A term, viewed as a morphism of the presented category (the
    carrier of a hom of [CPresentedCat] IS [CTerm Σ]). *)
Definition cquot {cs ds : list Colour} (t : CTerm Σ cs ds) :
  cs ~{CPresentedCat}~> ds := t.

(** The projection functor: identity on objects and morphisms. *)
Definition CPresentedProj : CFreeCat Σ ⟶ CPresentedCat :=
  @QuotientProj (CFreeCat Σ) (fun cs ds : list Colour => @CTermEqW cs ds)
    CTermEqW_Congruence.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The tensor on the presented category

    The parallel-composition bifunctor descends to the quotient
    because [CTermEqW] is closed under [CT_tens]. *)

Definition CPresented_Tensor : CPresentedCat ∏ CPresentedCat ⟶ CPresentedCat :=
  @Quotient_bifunctor (CFreeCat Σ) (fun cs ds : list Colour => @CTermEqW cs ds)
    CTermEqW_Congruence (CFreeCat_Tensor Σ)
    (fun x y f g Hf Hg => CTEW_tens (fst f) (fst g) (snd f) (snd g) Hf Hg).

(*
   本节说明幺半结构、幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition CPresented_Monoidal : @Monoidal CPresentedCat := {|
  I            := (nil : list Colour);
  tensor       := CPresented_Tensor;
  unit_left    := fun x => Quotient_iso (CFreeCat_unit_left Σ x);
  unit_right   := fun x => Quotient_iso (CFreeCat_unit_right Σ x);
  tensor_assoc := fun x y z => Quotient_iso (CFreeCat_tensor_assoc Σ x y z);
  to_unit_left_natural := fun x y g =>
    CTEW_termeq _ _ (cleft_unit_natural Σ Cdec g);
  from_unit_left_natural := fun x y g =>
    CTEW_termeq _ _ (cleft_unit_natural_from Σ Cdec g);
  to_unit_right_natural := fun x y g =>
    CTEW_termeq _ _ (cright_unit_natural Σ g);
  from_unit_right_natural := fun x y g =>
    CTEW_termeq _ _ (cfrom_right_unit_natural Σ g);
  to_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
    CTEW_termeq _ _ (cassoc_natural Σ g h i);
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
    CTEW_termeq _ _ (cfrom_assoc_natural Σ g h i);
  triangle_identity := fun x y =>
    CTEW_termeq _ _ (cfree_triangle Σ Cdec x y);
  pentagon_identity := fun x y z w =>
    CTEW_termeq _ _ (cfree_pentagon Σ Cdec x y z w)
|}.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CPresented_Braided : @BraidedMonoidal CPresentedCat :=
  @Build_BraidedMonoidal CPresentedCat
    CPresented_Monoidal  (* THE shared record *)
    (fun cs ds : list Colour => CT_braid cs ds)
    (fun x y g z w h => CTEW_termeq _ _ (cfree_braid_square Σ g h))
    (fun x y z => CTEW_termeq _ _ (cfree_hexagon Σ x y z))
    (fun x y z => CTEW_termeq _ _ (cfree_hexagon_sym Σ x y z)).

Definition CPresented_Symmetric : @SymmetricMonoidal CPresentedCat :=
  @Build_SymmetricMonoidal CPresentedCat
    CPresented_Braided
    (fun x y => CTEW_termeq _ _ (cfree_braid_invol Σ x y)).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CPresented_Strict : @StrictMonoidal CPresentedCat := {|
  strict_is_monoidal    := CPresented_Monoidal;  (* THE shared record *)
  strict_assoc_obj      := fun x y z => eq_sym (app_assoc x y z);
  strict_unit_left_obj  := fun x => app_nil_l x;
  strict_unit_right_obj := fun x => app_nil_r x
|}.
Next Obligation. exact (CTermEqW_refl _). Qed.
Next Obligation. exact (CTermEqW_refl _). Qed.
Next Obligation. exact (CTermEqW_refl _). Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CPresentedColouredPROP : ColouredPROP Colour :=
  Build_ColouredPROP Colour
    CPresentedCat
    CPresented_Strict
    CPresented_Symmetric

    (* [strict_is_monoidal CPresented_Strict] and
       [braided_is_monoidal (symmetric_is_braided CPresented_Symmetric)]
       both reduce to the literal term [CPresented_Monoidal]. *)
    eq_refl

    (* Objects of [CPresentedCat] are literally the colour words. *)
    (fun cs : list Colour => cs)

    (* [I] of [CPresented_Monoidal] is the literal [[]]. *)
    eq_refl

    (* [fobj CPresented_Tensor (cs, ds)] reduces to [cs ++ ds]. *)
    (fun cs ds : list Colour => eq_refl).

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The tensor-then-project and project-then-tensor composites that
    the tensor comparison relates. *)
Definition CPresented_ap_dom : CFreeCat Σ ∏ CFreeCat Σ ⟶ CPresentedCat :=
  CPresented_Tensor ◯ (CPresentedProj ∏⟶ CPresentedProj).

Definition CPresented_ap_cod : CFreeCat Σ ∏ CFreeCat Σ ⟶ CPresentedCat :=
  CPresentedProj ◯ CFreeCat_Tensor Σ.

(** Both directions of the tensor comparison are families of
    identities; naturality is [ctm_id_swap]. *)
Definition CPresented_ap_to : CPresented_ap_dom ⟹ CPresented_ap_cod :=
  @Build_Transform' (CFreeCat Σ ∏ CFreeCat Σ) CPresentedCat
    CPresented_ap_dom CPresented_ap_cod
    (fun p => CT_id ((fst p ++ snd p)%list))
    (fun p q f => CTEW_termeq _ _ (ctm_id_swap (CT_tens (fst f) (snd f)))).

Definition CPresented_ap_from : CPresented_ap_cod ⟹ CPresented_ap_dom :=
  @Build_Transform' (CFreeCat Σ ∏ CFreeCat Σ) CPresentedCat
    CPresented_ap_cod CPresented_ap_dom
    (fun p => CT_id ((fst p ++ snd p)%list))
    (fun p q f => CTEW_termeq _ _ (ctm_id_swap (CT_tens (fst f) (snd f)))).

(*
   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CPresented_ap_iso :
  @Isomorphism
    (@Category.Instance.Fun.Fun (CFreeCat Σ ∏ CFreeCat Σ) CPresentedCat)
    CPresented_ap_dom CPresented_ap_cod :=
  @Build_Isomorphism
    (@Category.Instance.Fun.Fun (CFreeCat Σ ∏ CFreeCat Σ) CPresentedCat)
    CPresented_ap_dom CPresented_ap_cod
    CPresented_ap_to CPresented_ap_from
    (fun p => CTEW_termeq _ _ (ctm_comp_id_tens (fst p) (snd p)))
    (fun p => CTEW_termeq _ _ (ctm_comp_id_tens (fst p) (snd p))).

Program Definition CPresentedProj_Monoidal :
  @MonoidalFunctor (CFreeCat Σ) CPresentedCat
    (CFreeCat_Monoidal Σ Cdec) CPresented_Monoidal CPresentedProj := {|
  pure_iso := iso_id;
  ap_functor_iso := CPresented_ap_iso;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc := fun x y z =>
    @tensor_assoc CPresentedCat CPresented_Monoidal x y z;
  monoidal_unit_left := fun x =>
    CTEW_termeq _ _
      (CTE_sym _ _ (ctm_collapse_r (CT_cast (app_nil_l x))));
  monoidal_unit_right := fun x =>
    CTEW_termeq _ _
      (CTE_sym _ _ (ctm_collapse_r (CT_cast (app_nil_r x))));
  monoidal_assoc := fun x y z =>
    CTEW_termeq _ _
      (CTE_trans _ _ _
         (ctm_collapse_r (CT_cast (eq_sym (app_assoc x y z))))
         (CTE_sym _ _
            (ctm_collapse_l (CT_cast (eq_sym (app_assoc x y z))))))
|}.

(** Both comparison maps of the projection are identities on the
    nose, so the projection is STRICT monoidal, with [eq_refl] object
    equalities. *)

Lemma CPresentedProj_pure_id :
  to (@pure_iso _ _ _ _ CPresentedProj CPresentedProj_Monoidal)
  ≈[CPresentedCat] @id CPresentedCat (nil : list Colour).
Proof. exact (CTermEqW_refl _). Qed.

Lemma CPresentedProj_ap_id (x y : list Colour) :
  to (@ap_iso _ _ _ _ CPresentedProj CPresentedProj_Monoidal x y)
  ≈[CPresentedCat] @id CPresentedCat ((x ++ y)%list).
Proof. exact (CTermEqW_refl _). Qed.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CPresentedProj_Strict :
  @StrictMonoidalFunctor (CFreeCat Σ) CPresentedCat
    (CFreeCat_Monoidal Σ Cdec) CPresented_Monoidal CPresentedProj := {|
  strict_functor_is_monoidal := CPresentedProj_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun x y => eq_refl
|}.
Next Obligation. exact (CTermEqW_refl _). Qed.
Next Obligation. exact (CTermEqW_refl _). Qed.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CPresentedProj_braid (cs ds : list Colour) :
  fmap[CPresentedProj] (@braid (CFreeCat Σ) (CFreeCat_Braided Σ Cdec) cs ds)
    ∘ to (@ap_iso _ _ _ _ CPresentedProj CPresentedProj_Monoidal cs ds)
  ≈[CPresentedCat]
  to (@ap_iso _ _ _ _ CPresentedProj CPresentedProj_Monoidal ds cs)
    ∘ @braid CPresentedCat CPresented_Braided cs ds.
Proof.
  exact (CTEW_termeq _ _ (ctm_id_swap (CT_braid cs ds))).
Qed.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CPresentedProj_Braided :
  @BraidedMonoidalFunctor (CFreeCat Σ) CPresentedCat
    (CFreeCat_Braided Σ Cdec) CPresented_Braided CPresentedProj :=
  @Build_BraidedMonoidalFunctor (CFreeCat Σ) CPresentedCat
    (CFreeCat_Braided Σ Cdec) CPresented_Braided CPresentedProj
    CPresentedProj_Monoidal
    (fun x y => CTEW_termeq _ _ (ctm_id_swap (CT_braid x y))).

(** A braided monoidal functor between symmetric monoidal categories
    IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition CPresentedProj_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat Σ) CPresentedCat
    (CFreeCat_Symmetric Σ Cdec) CPresented_Symmetric CPresentedProj :=
  CPresentedProj_Braided.

(** ** Machine-checked sanity

    Each [Example] holds by [eq_refl] (or a single constructor),
    witnessing that the corresponding field or action is definitional;
    any regression in the shared-record wiring is caught here rather
    than at a distant use site. *)

(** The coherence between the strict and symmetric [Monoidal] paths
    is the reflexivity proof itself. *)
Example CPresentedColouredPROP_coherence_is_refl :
  @cprop_monoidal_coherence Colour CPresentedColouredPROP = eq_refl := eq_refl.

(** The object correspondence is the identity on colour words. *)
Example CPresentedColouredPROP_of_list_id (cs : list Colour) :
  cprop_of_list (ColouredPROP := CPresentedColouredPROP) cs = cs := eq_refl.

(** Tensor-on-objects is literally concatenation, with [eq_refl]
    proof. *)
Example CPresentedColouredPROP_tensor_app_is_refl (cs ds : list Colour) :
  cprop_tensor_app (ColouredPROP := CPresentedColouredPROP) cs ds = eq_refl
  := eq_refl.

(** The singleton wire object for colour [c] is the literal
    one-element word [c :: nil]. *)
Example CPresentedColouredPROP_wire (c : Colour) :
  wire (P := CPresentedColouredPROP) c = (c :: nil) := eq_refl.

(** The projection functor acts as the identity on terms. *)
Example CPresentedProj_fmap_id_on_terms {cs ds : list Colour}
  (t : CTerm Σ cs ds) :
  fmap[CPresentedProj] t = cquot t := eq_refl.

(** Every axiom of the theory holds in the presented category. *)
Example CPresented_axioms_hold {cs ds : list Colour}
  (s t : CTerm Σ cs ds) (H : csmt_eqs E cs ds s t) :
  cquot s ≈[CPresentedCat] cquot t := CTEW_ax s t H.

End Presented.

Arguments CTermEqW {Colour} E {cs ds} _ _.
Arguments CPresentedCat {Colour} E : assert.
Arguments cquot {Colour} E {cs ds} t : assert.
Arguments CPresentedProj {Colour} E : assert.
Arguments CPresented_Tensor {Colour} E : assert.
Arguments CPresented_Monoidal {Colour} E Cdec : assert.
Arguments CPresented_Braided {Colour} E Cdec : assert.
Arguments CPresented_Symmetric {Colour} E Cdec : assert.
Arguments CPresented_Strict {Colour} E Cdec : assert.
Arguments CPresentedColouredPROP {Colour} E Cdec : assert.
Arguments CPresentedProj_Monoidal {Colour} E Cdec : assert.
Arguments CPresentedProj_Strict {Colour} E Cdec : assert.
Arguments CPresentedProj_braid {Colour} E Cdec cs ds : assert.
Arguments CPresentedProj_Braided {Colour} E Cdec : assert.
Arguments CPresentedProj_Symmetric {Colour} E Cdec : assert.
