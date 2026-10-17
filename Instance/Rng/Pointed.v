Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book: Awodey, "Category Theory", §9.3, Example 9.10, printed
 nLab:      https://ncatlab.org/nlab/show/free+functor
 nLab:      https://ncatlab.org/nlab/show/pointed+object
 Wikipedia: https://en.wikipedia.org/wiki/Polynomial_ring

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The underlying-set functor of commutative rings *)

Program Definition CRng_Forget : CRng ⟶ Sets := {|
  fobj := fun A => rig_setoid (`1 A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** ** Pointed commutative rings *)

(** Objects are pairs (A, a); morphisms are the ring homomorphisms
    carrying the point.  This is Construction/Elements.v's category of
    elements, not a fresh construction. *)
Definition CRngPt : Category := Elements CRng_Forget.

Definition CRngPt_Forget : CRngPt ⟶ CRng := Elements_proj CRng_Forget.

(** The hom-type is the point-preservation condition, definitionally. *)
Example CRngPt_hom_unfold (P Q : CRngPt) :
  (P ~{CRngPt}~> Q)
    = ∃ f : `1 P ~{CRng}~> `1 Q, rig_map (`1 f) (`2 P) ≈ `2 Q
  := eq_refl.

(** ** The polynomial ring, pointed at the indeterminate *)

Definition PolyCRng (A : CRng) : CRng := (PolyRing (`1 A); poly_comm (`1 A)).

Definition PolyPt (A : CRng) : CRngPt := (PolyCRng A; @poly_x (`1 A)).

(** The coefficient inclusion, as a morphism of commutative rings.  The
    membership witness of [CRng_Sub] is trivial. *)
Definition poly_pointed_arrow (A : CRng)
  : A ~{CRng}~> CRngPt_Forget (PolyPt A) :=
  (poly_const (`1 A); I).

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example poly_packagings_agree_ring (A : CRng) :
  kalg_ring (PolyAlg A) = `1 (`1 (PolyPt A)) := eq_refl.

Example poly_packagings_agree_unit (A : CRng) :
  kalg_unit (PolyAlg A) = `1 (poly_pointed_arrow A) := eq_refl.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma poly_pointed_universal (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) :
  ∃! g : PolyPt A ~{CRngPt}~> Q,
    h ≈ fmap[CRngPt_Forget] g ∘ poly_pointed_arrow A.
Proof.
  unshelve econstructor.
  - unshelve refine ((_; I); _).
    + refine (poly_extend (`1 h) (`2 Q) (`2 A) _).
      intro c; exact (`2 (`1 Q) (`2 Q) (rig_map (`1 h) c)).
    + simpl; reflexivity.
  - intro c; simpl; reflexivity.
  - intros v Hv t; simpl.
    symmetry.
    apply (poly_extend_unique (`1 h) (`2 Q) (`1 (`1 v))).
    + intro c; symmetry; exact (Hv c).
    + exact (`2 v).
Defined.

Definition poly_pointed_universal_arrow (A : CRng)
  : UniversalArrow A CRngPt_Forget :=
  universal_arrow_from_UMP A CRngPt_Forget (PolyPt A)
    (poly_pointed_arrow A) (poly_pointed_universal A).

(** ** The left adjoint and the adjunction

    Both come out of the generic machinery with no further proof — the
    route Construction/Free/Quiver.v and Instance/Mod/Free.v take. *)

Definition PolyPointed : CRng ⟶ CRngPt :=
  LeftAdjointFunctorFromUniversalArrows CRngPt_Forget
    poly_pointed_universal_arrow.

Definition poly_pointed_adjunction : PolyPointed ⊣ CRngPt_Forget :=
  AdjunctionFromUniversalArrows CRngPt_Forget poly_pointed_universal_arrow.

(** The left adjoint's object part is the pointed polynomial ring, and
    the universal arrow is the coefficient inclusion — both on the nose. *)
Example PolyPointed_obj (A : CRng) : PolyPointed A = PolyPt A := eq_refl.

Example poly_pointed_point_is_x (A : CRng) :
  `2 (PolyPointed A) = @poly_x (`1 A) := eq_refl.

Example poly_pointed_arrow_is_const (A : CRng) :
  @arrow _ _ A CRngPt_Forget (poly_pointed_universal_arrow A)
    = poly_pointed_arrow A := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition poly_pointed_unit (A : CRng)
  : A ~{CRng}~> CRngPt_Forget (PolyPointed A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ poly_pointed_adjunction A.

Example poly_pointed_unit_is_const (A : CRng)
  (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (poly_pointed_unit A)) c = @pt_const (`1 A) c := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem poly_pointed_transpose_is_evaluation (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q)
  (g : PolyPt A ~{CRngPt}~> Q)
  (Hg : h ≈ fmap[CRngPt_Forget] g ∘ poly_pointed_arrow A)
  (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 g)) t ≈ peval (`1 h) (`2 Q) t.
Proof.
  apply (poly_extend_unique (`1 h) (`2 Q) (`1 (`1 g))).
  - intro c; symmetry; exact (Hg c).
  - exact (`2 g).
Qed.

Corollary poly_pointed_adj_transpose_evaluates (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    ≈ peval (`1 h) (`2 Q) t.
Proof.
  apply poly_pointed_transpose_is_evaluation.
  symmetry.
  exact (iso_to_from (@adj _ _ _ _ poly_pointed_adjunction A Q) h).
Qed.

(** ** The left adjoint relabels coefficients

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a
    constant has to be proved. *)
Lemma poly_pointed_fmap_const {A B : CRng} (u : A ~{CRng}~> B)
  (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (`1 (fmap[PolyPointed] u))) (@pt_const (`1 A) c)
    ≈ @pt_const (`1 B) (rig_map (`1 u) c).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (poly_pointed_universal_arrow A)
              (@arrow _ _ B CRngPt_Forget
                 (poly_pointed_universal_arrow B) ∘ u)) c).
Qed.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Int_pointed (b : Z) : CRngPt := (Int_CRng; b).

Definition zpoly_pointed_eval (b : Z)
  : PolyPt Int_CRng ~{CRngPt}~> Int_pointed b.
Proof.
  unshelve refine ((_; I); _).
  - exact (zpoly_eval Int_Ring b).
  - simpl; reflexivity.
Defined.

Example zpoly_pointed_eval_computes :
  rig_map (`1 (`1 (zpoly_pointed_eval 3%Z))) zpoly_sample = 16%Z := eq_refl.

Example zpoly_pointed_eval_at_x (b : Z) :
  rig_map (`1 (`1 (zpoly_pointed_eval b))) (@poly_x Int_Ring) = b := eq_refl.
