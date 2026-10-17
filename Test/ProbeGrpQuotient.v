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

(*
   本节说明 ProbeGrpQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 ProbeGrpQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section BigZero.

Context {G K : GrpObject@{big big big}}.

Definition control_big_zero : G ~{Grp}~> K := @zero_mor Grp Grp_Zero G K.

End BigZero.

(** ** Positive controls for the strict identifications that DO hold *)

Section Positive.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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
