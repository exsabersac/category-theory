(*
   本文件给出 Free 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/free+module
 nLab:      https://ncatlab.org/nlab/show/basis+of+a+vector+space
 Wikipedia: https://en.wikipedia.org/wiki/Free_module
 Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 Book: Mac Lane, ibid., §IV.1, printed p. 79 —
 Book: Riehl, Category Theory in Context, §4.0, printed p. 131 —

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeVect.

Context (F : FieldObject).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Vct_F_is_RMod : Vct_F F = RMod (field_ring F) := eq_refl.

Definition Vct_Forget : Vct_F F ⟶ Sets := RMod_Forget (field_ring F).

Example Vct_Forget_is_RMod_Forget :
  Vct_Forget = RMod_Forget (field_ring F) := eq_refl.

(** ** The free vector space on a set, and its basis insertion *)

Definition FreeVectObject (X : Sets) : Vct_F F := FreeModObject X.

Definition free_vect_insert (X : Sets)
  : X ~{Sets}~> Vct_Forget (FreeVectObject X) := fv_insert X.

(** ** Mac Lane §III.1: ⟨V_X, j⟩ is a universal arrow

    Every function from X into the underlying set of a vector space W
    extends to one and only one linear map V_X ⟶ W. *)
Theorem free_vect_universal (X : Sets) :
  ∀ (W : Vct_F F) (h : X ~{Sets}~> Vct_Forget W),
    ∃! g : FreeVectObject X ~{Vct_F F}~> W,
      h ≈ fmap[Vct_Forget] g ∘ free_vect_insert X.
Proof. exact (free_module_universal X). Qed.

Definition free_vect_universal_arrow (X : Sets)
  : UniversalArrow X Vct_Forget := free_module_universal_arrow X.

(** The same content in the direct encoding, where the universal object
    is named rather than projected out of a comma category. *)
Definition free_vect_AUniversalArrow (X : Sets)
  : AUniversalArrow X Vct_Forget (FreeVectObject X) :=
  free_module_AUniversalArrow (field_ring F) X.

(** ** Mac Lane §IV.1 and Riehl §4.0: the adjunction

    The principal artifact of this issue. *)

Definition FreeVect : Sets ⟶ Vct_F F := FreeMod (field_ring F).

Definition free_vect_adjunction : FreeVect ⊣ Vct_Forget :=
  free_module_adjunction (field_ring F).

Example FreeVect_obj (X : Sets) : FreeVect X = FreeVectObject X := eq_refl.

Example free_vect_arrow_is_insert (X : Sets) :
  @arrow _ _ X Vct_Forget (free_vect_universal_arrow X)
    = free_vect_insert X := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_vect_unit (X : Sets)
  : X ~{Sets}~> Vct_Forget (FreeVect X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_vect_adjunction X.

Example free_vect_unit_is_insert (X : Sets) (x : carrier X) :
  free_vect_unit X x = free_vect_insert X x := eq_refl.

Definition free_vect_counit (W : Vct_F F)
  : FreeVect (Vct_Forget W) ~{Vct_F F}~> W :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_vect_adjunction W.

Theorem free_vect_counit_evaluates (W : Vct_F F)
  (t : @FVTerm (field_ring F) (Vct_Forget W)) :
  cmon_map (rm_hom (free_vect_counit W)) t
    ≈ fv_eval (@id Sets (Vct_Forget W)) t.
Proof. exact (free_module_counit_evaluates (field_ring F) W t). Qed.

(** ** Riehl's functoriality on maps of generating sets

    Relabelling the generating set relabels the basis vectors. *)
Lemma free_vect_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (rm_hom (fmap[FreeVect] u)) (fv_gen x) ≈ fv_gen (u x).
Proof. exact (@free_module_fmap_generators (field_ring F) X Y u x). Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_vect_restrict {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) : X ~{Sets}~> Vct_Forget W :=
  fv_transpose g.

Example free_vect_restrict_is_adj {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) :
  to (@adj _ _ _ _ free_vect_adjunction X W) g = free_vect_restrict g
  := eq_refl.

Lemma free_vect_restrict_extend {X : Sets} {W : Vct_F F}
  (h : X ~{Sets}~> Vct_Forget W) : free_vect_restrict (fv_extend h) ≈ h.
Proof. exact (fv_transpose_extend (field_ring F) h). Qed.

Lemma free_vect_extend_restrict {X : Sets} {W : Vct_F F}
  (g : FreeVect X ~{Vct_F F}~> W) : fv_extend (free_vect_restrict g) ≈ g.
Proof. exact (fv_extend_transpose (field_ring F) g). Qed.

(** *** Naturality in the set variable *)
Theorem free_vect_naturality_in_set {X Y : Sets} {W : Vct_F F}
  (g : FreeVect Y ~{Vct_F F}~> W) (u : X ~{Sets}~> Y) :
  free_vect_restrict (g ∘ fmap[FreeVect] u) ≈ free_vect_restrict g ∘ u.
Proof. exact (free_module_naturality_in_set (field_ring F) g u). Qed.

(** *** Naturality in the target space *)
Theorem free_vect_naturality_in_space {X : Sets} {W W' : Vct_F F}
  (k : W ~{Vct_F F}~> W') (g : FreeVect X ~{Vct_F F}~> W) :
  free_vect_restrict (k ∘ g) ≈ fmap[Vct_Forget] k ∘ free_vect_restrict g.
Proof. exact (free_module_naturality_in_module (field_ring F) k g). Qed.

(** ** The triangle identities *)

Corollary free_vect_triangle_left (X : Sets) :
  free_vect_counit (FreeVect X) ∘ fmap[FreeVect] (free_vect_unit X)
    ≈ @id (Vct_F F) (FreeVect X).
Proof. exact (free_module_triangle_left (field_ring F) X). Qed.

Corollary free_vect_triangle_right (W : Vct_F F) :
  fmap[Vct_Forget] (free_vect_counit W)
    ∘ free_vect_unit (Vct_Forget W) ≈ @id Sets (Vct_Forget W).
Proof. exact (free_module_triangle_right (field_ring F) W). Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_vect_finite_combination (X : Sets)
  (t : @FVTerm (field_ring F) X) :
  ∃ l : list (fv_pair (field_ring F) X), fv_eq t (fv_lc l).
Proof. exact (fv_normal_form t). Qed.

End FreeVect.

(* Only the one that changes anything: everything else discharged from
   the section already has [F] explicit. *)
Arguments free_vect_restrict {F X W} g.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — see the same device in Instance/Mod/Free.v. *)
Local Notation qgen  := (@fv_gen (field_ring Q_Field) TwoGens).
Local Notation qsmul := (@fv_smul (field_ring Q_Field) TwoGens).
Local Notation qplus := (@fv_plus (field_ring Q_Field) TwoGens).
Local Notation qzero := (@fv_zero (field_ring Q_Field) TwoGens).

(** ℚ as a vector space over itself. *)
Definition QLine : Vct_F Q_Field := Ring_RMod (field_ring Q_Field).

(** The assignment e₀ ↦ 3, e₁ ↦ 5. *)
Definition q_probe : TwoGens ~{Sets}~> Vct_Forget Q_Field QLine.
Proof.
  unshelve refine {| morphism := fun b : carrier TwoGens => if b then (3 # 1)%Q else (5 # 1)%Q |}.
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(** The linear extension computes: 2·e₀ + e₁ ↦ 2·3 + 5 = 11.  This is
    [eq_refl] on the CARRIER ℚ — the convertibility exception, not a
    statement about morphisms. *)
Example q_free_extend_computes :
  fv_eval q_probe (qplus (qsmul (2 # 1)%Q (qgen true)) (qgen false))
  = (11 # 1)%Q := eq_refl.

Example q_free_extend_generator_true :
  fv_eval q_probe (qgen true) = (3 # 1)%Q := eq_refl.

Example q_free_extend_generator_false :
  fv_eval q_probe (qgen false) = (5 # 1)%Q := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** *** The basis insertion does not collapse

    The [1 ≉ 0] premise of Instance/Mod/Free.v's general theorem is
    [field_one_neq_zero], a FIELD of [FieldObject], so over a field it
    costs nothing; only the decider is supplied. *)
Theorem free_vect_basis_distinct :
  fv_eq (qgen true) (qgen false) → False.
Proof.
  intro He.
  pose proof (free_module_basis_injective two_gens_dec
                (field_one_neq_zero Q_Field) true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_vect_basis_independent (r s : Q) :
  fv_eq (qplus (qsmul r (qgen true)) (qsmul s (qgen false))) qzero →
  ((r == 0)%Q * (s == 0)%Q)%type.
Proof.
  exact (@free_module_two_independent (field_ring Q_Field) TwoGens
           two_gens_dec true false two_gens_distinct r s).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_vect_half_not_one :
  fv_eq (qsmul (1 # 2)%Q (qgen true)) (qsmul (1 # 1)%Q (qgen true)) → False.
Proof.
  intro He.
  pose proof (@free_module_scalars_faithful (field_ring Q_Field) TwoGens
                (1 # 2)%Q (1 # 1)%Q true He) as Hq.
  compute in Hq; discriminate Hq.
Qed.
