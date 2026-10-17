Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Theory.Lawvere.

Generalizable All Variables.

(** * Lawvere theories meet the PROP spine *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   nLab:      https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** 1. The cartesian symmetric monoidal structure on a Lawvere theory *)

Section LawvereMonoidal.

Context (T : LawvereTheory).

(** Tensor := ×, unit := 1, via [Cartesian_Monoidal] (= [CC_Monoidal]). *)
Definition Lawvere_Monoidal : @Monoidal (@law_cat T) :=
  @Cartesian_Monoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** The braiding is the product swap [⟨exr, exl⟩]. *)
Definition Lawvere_Braided : @BraidedMonoidal (@law_cat T) :=
  @CC_BraidedMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** Symmetry: [swap ∘ swap ≈ id]. *)
Definition Lawvere_Symmetric : @SymmetricMonoidal (@law_cat T) :=
  @CC_SymmetricMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** The full cartesian-monoidal packaging (relevance + semicartesian),
    i.e. the Fox-side data: diagonal [⟨id, id⟩] and eliminate [one]. *)
Definition Lawvere_CartesianMonoidal : @CartesianMonoidal (@law_cat T) :=
  @CC_CartesianMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** Sanity, machine-checked: the monoidal structures underlying the
    braided/symmetric packagings are [Lawvere_Monoidal] itself, on the
    nose.  This definitional agreement is what lets the PROP coherence
    field below be a single equality hypothesis. *)
Example Lawvere_Symmetric_monoidal_coherence :
  @braided_is_monoidal (@law_cat T)
    (@symmetric_is_braided (@law_cat T) Lawvere_Symmetric)
  = Lawvere_Monoidal := eq_refl.

End LawvereMonoidal.

(** ** 2. The PROP on a strict Lawvere theory, and interpretation *)

Section LawverePROP.

Context (T : LawvereTheory).

(** The strictness pack: the in-tree PROP/interpretation machinery
    requires a strict target, and a general Lawvere theory's cartesian
    monoidal structure is only weakly monoidal, so strictness is a
    hypothesis — expected to be satisfied on skeletal instances (objects
    literally the natural numbers) with [coh := eq_refl] and the
    strictness object equalities by nat induction; the in-tree witness
    awaits the base's monoidal assembly (header note). *)
Context (SM : @StrictMonoidal (@law_cat T)).
Context (coh : @strict_is_monoidal (@law_cat T) SM = Lawvere_Monoidal T).

(** The unit of the strict path is [law_of_nat 0]: transport
    [law_zero_terminal] along [coh]. *)
Definition Lawvere_prop_unit_zero :
  @I (@law_cat T) (@strict_is_monoidal (@law_cat T) SM)
  = @law_of_nat T 0%nat :=
  eq_trans
    (f_equal (fun M : @Monoidal (@law_cat T) => @I (@law_cat T) M) coh)
    (eq_sym (@law_zero_terminal T)).

(** Tensor on canonical objects is addition: transport
    [law_plus_product] along [coh]. *)
Definition Lawvere_prop_tensor_plus (m n : nat) :
  (@law_of_nat T m ⨂[@strict_is_monoidal (@law_cat T) SM] @law_of_nat T n)%object
  = @law_of_nat T (m + n)%nat :=
  eq_trans
    (f_equal
       (fun M : @Monoidal (@law_cat T) =>
          (@law_of_nat T m ⨂[M] @law_of_nat T n)%object) coh)
    (@law_plus_product T m n).

(** The PROP on [law_cat T]: strict path [SM], symmetric path the
    cartesian braiding of section 1, coherence the hypothesis [coh]
    (typechecking because [braided_is_monoidal (symmetric_is_braided
    (Lawvere_Symmetric T))] is definitionally [Lawvere_Monoidal T]),
    and object correspondence [law_of_nat]. *)
Definition Lawvere_PROP : PROP := {|
  prop_cat := @law_cat T;
  prop_strict := SM;
  prop_symmetric := Lawvere_Symmetric T;
  prop_monoidal_coherence := coh;
  prop_of_nat := @law_of_nat T;
  prop_unit_zero := Lawvere_prop_unit_zero;
  prop_tensor_plus := Lawvere_prop_tensor_plus
|}.

(** *** Interpretation of a free PROP in the Lawvere theory

    The side conditions are those of [Construction/PROP/Interp.v] /
    [Universal.v]: a [Prop] reflection of the hom equivalence and
    decidable object equality (powering the axiom-free UIP on objects). *)

Context {HP : HomEqProp (@law_cat T)}.
Context {OD : @ObjDecEq (@law_cat T)}.

Context (Σ : Signature).

(** A valuation of the generators of [Σ] in [law_cat T], along
    [law_of_nat] — definitionally a [Valuation (Lawvere_PROP) Σ]. *)
Context (v : ∀ m n : nat, Σ m n → (@law_of_nat T m ~{@law_cat T}~> @law_of_nat T n)).

Definition Lawvere_Valuation : Valuation Lawvere_PROP Σ := v.

(** The induced interpretation functor out of the free PROP ([FreeCat Σ]
    is the underlying category of [FreePROP Σ]), instantiating the
    in-tree universal-property machinery at [Lawvere_PROP]. *)
Definition Lawvere_PROP_interp : FreeCat Σ ⟶ @law_cat T :=
  @InterpF Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** Machine-checked: the interpretation extends the valuation — every
    generator is sent to its assigned [law_cat T]-morphism, on the nose. *)
Example Lawvere_PROP_interp_extends (m n : nat) (g : Σ m n) :
  fmap[Lawvere_PROP_interp] (T_gen g) ≈ v m n g.
Proof. reflexivity. Qed.

(** The strong monoidal packaging, over the strict path [SM]. *)
Definition Lawvere_PROP_interp_Monoidal :
  @MonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Monoidal Σ)
    (@strict_is_monoidal (@law_cat T) SM) Lawvere_PROP_interp :=
  @InterpF_Monoidal Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** The strict monoidal packaging: the object comparisons are the
    transported [law_zero_terminal] / [law_plus_product], verbatim. *)
Definition Lawvere_PROP_interp_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Monoidal Σ)
    (@strict_is_monoidal (@law_cat T) SM) Lawvere_PROP_interp :=
  @InterpF_Strict Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** The braided packaging, landing in the cartesian braiding of
    section 1 — the braid-square requirement of [Interp.v] is met by
    the symmetry [swap = ⟨exr, exl⟩] of the Lawvere theory. *)
Definition Lawvere_PROP_interp_Braided :
  @BraidedMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Braided Σ)
    (@symmetric_is_braided (@law_cat T) (Lawvere_Symmetric T))
    Lawvere_PROP_interp :=
  @InterpF_Braided Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** The symmetric packaging, at [Lawvere_Symmetric]. *)
Definition Lawvere_PROP_interp_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Symmetric Σ)
    (Lawvere_Symmetric T) Lawvere_PROP_interp :=
  @InterpF_Symmetric Σ Lawvere_PROP HP OD Lawvere_Valuation.

End LawverePROP.

