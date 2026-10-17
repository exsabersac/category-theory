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

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   nLab:      https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section LawvereMonoidal.

Context (T : LawvereTheory).

(** Tensor := ×, unit := 1, via [Cartesian_Monoidal] (= [CC_Monoidal]). *)
Definition Lawvere_Monoidal : @Monoidal (@law_cat T) :=
  @Cartesian_Monoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** 本节：The braiding product swap [⟨exr, exl⟩]. （已译） *)
Definition Lawvere_Braided : @BraidedMonoidal (@law_cat T) :=
  @CC_BraidedMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** Symmetry: [swap ∘ swap ≈ id]. *)
Definition Lawvere_Symmetric : @SymmetricMonoidal (@law_cat T) :=
  @CC_SymmetricMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** 本节：The full cartesian-monoidal packaging (relevance + semicartesian),
 i.e. Fox-side data: diagonal [⟨id, id⟩] eliminate [one]. （已译） *)
Definition Lawvere_CartesianMonoidal : @CartesianMonoidal (@law_cat T) :=
  @CC_CartesianMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(*
   本节说明幺半结构、幺半群、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Lawvere_Symmetric_monoidal_coherence :
  @braided_is_monoidal (@law_cat T)
    (@symmetric_is_braided (@law_cat T) Lawvere_Symmetric)
  = Lawvere_Monoidal := eq_refl.

End LawvereMonoidal.

(* 相关说明。 （已译） *)

Section LawverePROP.

Context (T : LawvereTheory).

(*
   本节说明幺半结构、幺半群、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (SM : @StrictMonoidal (@law_cat T)).
Context (coh : @strict_is_monoidal (@law_cat T) SM = Lawvere_Monoidal T).

(** 本节：The unit strict path [law_of_nat 0]: transport
 [law_zero_terminal] along [coh]. （已译） *)
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

(*
   本节说明Lawvere 理论、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Lawvere_PROP : PROP := {|
  prop_cat := @law_cat T;
  prop_strict := SM;
  prop_symmetric := Lawvere_Symmetric T;
  prop_monoidal_coherence := coh;
  prop_of_nat := @law_of_nat T;
  prop_unit_zero := Lawvere_prop_unit_zero;
  prop_tensor_plus := Lawvere_prop_tensor_plus
|}.

(*
   本节说明hom、等价、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context {HP : HomEqProp (@law_cat T)}.
Context {OD : @ObjDecEq (@law_cat T)}.

Context (Σ : Signature).

(** A valuation of the generators of [Σ] in [law_cat T], along
    [law_of_nat] — definitionally a [Valuation (Lawvere_PROP) Σ]. *)
Context (v : ∀ m n : nat, Σ m n → (@law_of_nat T m ~{@law_cat T}~> @law_of_nat T n)).

Definition Lawvere_Valuation : Valuation Lawvere_PROP Σ := v.

(*
   本节说明函子、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Lawvere_PROP_interp : FreeCat Σ ⟶ @law_cat T :=
  @InterpF Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** Machine-checked: interpretation extends valuation — every
 generator sent assigned [law_cat T]-态射, nose. （已译） *)
Example Lawvere_PROP_interp_extends (m n : nat) (g : Σ m n) :
  fmap[Lawvere_PROP_interp] (T_gen g) ≈ v m n g.
Proof. reflexivity. Qed.

(** 本节：The strong monoidal packaging, over strict path [SM]. （已译） *)
Definition Lawvere_PROP_interp_Monoidal :
  @MonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Monoidal Σ)
    (@strict_is_monoidal (@law_cat T) SM) Lawvere_PROP_interp :=
  @InterpF_Monoidal Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** The strict monoidal packaging: 对象 comparisons the
 transported [law_zero_terminal] / [law_plus_product], verbatim. （已译） *)
Definition Lawvere_PROP_interp_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Monoidal Σ)
    (@strict_is_monoidal (@law_cat T) SM) Lawvere_PROP_interp :=
  @InterpF_Strict Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** 本节：The braided packaging, landing cartesian braiding of
 section 1 — braid-square requirement [Interp.v] met by
 symmetry [swap = ⟨exr, exl⟩] Lawvere theory. （已译） *)
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

