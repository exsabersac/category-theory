(*
   本文件为测试：ProbeGrpQuotient。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Kernel.
Require Import Category.Instance.Grp.Quotient.Colimit.

Generalizable All Variables.

(** ** Negative 1: the kernel subgroup group is not [Grp_kernel] *)

(* POSITIVE CONTROL: the carriers ARE convertible. *)
Example control_kernel_carrier {G K : GrpObject} (h : G ~{Grp}~> K) :
  carrier (SubgroupGrp (KernelNS h)) = carrier (Grp_kernel h).
Proof. reflexivity. Qed.

(* NEGATIVE: the whole records are not. *)
Fail Definition negative_kernel_record {G K : GrpObject} (h : G ~{Grp}~> K) :
  SubgroupGrp (KernelNS h) = Grp_kernel h := eq_refl.

(** ** Negative 2: the mediator triangle is `≈` and not Leibniz *)

(* POSITIVE CONTROL: the `≈` form holds, pointwise by reflexivity. *)
Example control_med_triangle {G K : GrpObject} (N : NormalSubgroup G)
  (x : Kills N K) : quot_med N x ∘ quot_proj N ≈ `1 x.
Proof. exact (quot_med_commutes N x). Qed.

(* NEGATIVE: the Leibniz form does not. *)
Fail Definition negative_med_triangle {G K : GrpObject} (N : NormalSubgroup G)
  (x : Kills N K) : quot_med N x ∘ quot_proj N = `1 x := eq_refl.

(** ** Negative 3: [GrpImage_unit] is opaque *)

(* POSITIVE CONTROL: the equation the opaque lemma carries IS accessible,
   which is what [image_med] uses instead of the witness. *)
Example control_image_unit_equation {G K : GrpObject} (h : G ~{Grp}~> K) :
  grp_map h (`1 (GrpImage_unit h)) ≈ grp_unit K.
Proof. exact (`2 (GrpImage_unit h)). Qed.

(* NEGATIVE: the witness itself does not reduce to the unit. *)
Fail Definition negative_image_unit_witness {G K : GrpObject}
  (h : G ~{Grp}~> K) : `1 (GrpImage_unit h) = grp_unit G := eq_refl.

(** ** Boundary 4, lifted by #450: zero morphisms in [Grp] above [Set] *)

Monomorphic Universe big.
Monomorphic Constraint Set < big.

(* POSITIVE CONTROL: the quotient machinery itself carries no such pin --
   [QuotientGrp] and its universal element are formable at a group whose
   universes are declared strictly above [Set].  This is the half that
   said the pin belonged to [Grp_Zero] (until #450 lifted it) and not to
   this development. *)
Section BigCarrier.

Context {G : GrpObject@{big big big}}.
Context (N : NormalSubgroup@{big big big big} G).

Definition control_big_quotient : GrpObject@{big big big} := QuotientGrp N.

Definition control_big_projection : G ~{Grp}~> control_big_quotient :=
  quot_proj N.

Definition control_big_universal :
  AUniversalElement (KillsFunctor N) (QuotientGrp N) :=
  quot_universal_element N.

Definition control_big_kernel {K : GrpObject@{big big big}}
  (h : G ~{Grp}~> K) : NormalSubgroup G := KernelNS h.

Definition control_big_first_iso {K : GrpObject@{big big big}}
  (h : G ~{Grp}~> K) :
  QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h :=
  first_isomorphism_theorem h.

End BigCarrier.

(* CONTROL, formerly the NEGATIVE of boundary (4): the zero morphism at the
   same universes.  Until #450 this was the guarded negative
   [negative_big_zero], and stripping the guard reported "Cannot enforce
   Set = big"; since
   #450 annotated [Grp_Zero] it is accepted. *)
Section BigZero.

Context {G K : GrpObject@{big big big}}.

Definition control_big_zero : G ~{Grp}~> K := @zero_mor Grp Grp_Zero G K.

End BigZero.

(** ** Positive controls for the strict identifications that DO hold *)

Section Positive.

(* The comparison isomorphism of the first isomorphism theorem has the two
   mediators as its legs, by convertibility: the universal-element
   machinery of Theory/Universal/Element.v rebuilds neither. *)
Example positive_first_iso_to {G K : GrpObject} (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) = quot_med (KernelNS h) (image_elem h).
Proof. reflexivity. Qed.

Example positive_first_iso_from {G K : GrpObject} (h : G ~{Grp}~> K) :
  from (first_isomorphism_theorem h) = image_med h (quot_elem (KernelNS h)).
Proof. reflexivity. Qed.

(* The universal element's underlying homomorphism IS the projection. *)
Example positive_universal_elem {G : GrpObject} (N : NormalSubgroup G) :
  `1 (@aue_elem _ (KillsFunctor N) (QuotientGrp N) (quot_universal_element N))
    = quot_proj N.
Proof. reflexivity. Qed.

(* THE STRENGTH THAT WAS SAVED, AND THE RELATION THAT CARRIES IT.

   The PR "algebraic carriers are sets" (2026-09-17) truncated three
   relations in the Grp layer -- Test/ProbeGrpProp.v pins those from both
   sides -- and deliberately left Instance/Grp/Epi.v's [grp_coset_rel]
   alone, because truncating it would have cost
   [transposition_decides_image] its conclusion: the full
   [GrpImageDecidable f], and not a double negation of it.  Nothing in
   the tree guarded that decision until these two controls; an earlier
   revision of Test/ProbeGrpProp.v deferred it to "Test/ProbeGrpEpi*.v",
   a file that has never existed.

   The first control pins the relation's SORT -- a [Type]-valued
   [crelation], measured as [grp_coset_rel ... : crelation@{u u} H] by
   [About] under [Set Printing Universes] -- and the second pins the
   theorem's WHOLE statement, hypothesis and conclusion together, so that
   a later truncation of [grp_coset_rel], or a weakening of the
   conclusion to a [¬¬] form, breaks this file rather than passing
   silently. *)
Example positive_grp_coset_rel_is_type_valued
  {G H : GrpObject} (f : G ~{Grp}~> H) : crelation H :=
  grp_coset_rel f.

Example positive_transposition_decides_image_full
  {G H : GrpObject} (f : G ~{Grp}~> H)
  (t : SetoidPermutation (CosetPlusPtSetoid f))
  (Hbase : ∀ c, GrpImage f c →
             @equiv _ (is_setoid (CosetPlusPtSetoid f))
               (sperm_to t (inl c)) (inr ttt)) :
  GrpImageDecidable f :=
  transposition_decides_image f t Hbase.

End Positive.
