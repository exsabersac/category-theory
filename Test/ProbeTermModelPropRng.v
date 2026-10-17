(*
   本文件为测试：ProbeTermModelPropRng。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.Compose.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Vect.TensorAlgebra.
Require Import Category.Instance.Lie.
Require Import Category.Adjunction.Enveloping.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** ** 1. [mr_eq], Instance/Rng/MonoidRing.v *)

(* NEGATIVE.  The elimination into an arbitrary [Type]. *)
Fail Definition mr_eq_type_elim {R : RingObject} {M : MonSets}
  (s t : MRTerm R M) (He : mr_eq s t) : MRTerm R M :=
  ltac:(induction He; exact (mr_scal (rig_zero R))).

(* CONTROL.  The relation IS the monoid ring's `≈`, and is its own [Prop]
   mirror. *)
Example mr_pequiv_control {R : RingObject} {M : MonSets}
  (s t : MRTerm R M) (He : mr_eq s t) :
  @pequiv _ _ (rig_prop (MonoidRing R M)) s t := He.

(*
   本节说明 ProbeTermModelPropRng 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example mr_respects_control {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (Hcomm : MRComm phi psi) (s t : MRTerm R M) (He : mr_eq s t) :
  mreval phi psi s ≈ mreval phi psi t :=
  mreval_respects phi psi Hcomm s t He.

(** ** 2. [fr_eq], Instance/Rng/Free.v *)

Fail Definition fr_eq_type_elim {A : AbObject}
  (s t : FRTerm A) (He : fr_eq s t) : FRTerm A :=
  ltac:(induction He; exact fr_zero).

(* NEGATIVE.  The mediator's respectfulness with the elimination attempted
   directly at the [Type]-valued `≈`, i.e. the script the file carried before
   the relation moved. *)
Fail Definition fr_eval_type_elim {A : AbObject} (R : RingObject)
  (h : A ~{Ab}~> Rng_Forget_Ab R) (s t : FRTerm A) (He : fr_eq s t) :
  fr_eval h s ≈ fr_eval h t :=
  ltac:(induction He).

Example fr_pequiv_control {A : AbObject} (s t : FRTerm A) (He : fr_eq s t) :
  @pequiv _ _ (rig_prop (FreeRngAbObject A)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above: measured to compile
   against the baseline tree too. *)
Example fr_respects_control {A : AbObject} (R : RingObject)
  (h : A ~{Ab}~> Rng_Forget_Ab R) (s t : FRTerm A) (He : fr_eq s t) :
  fr_eval h s ≈ fr_eval h t :=
  fr_eval_respects R h s t He.

(** ** 3. [pt_eq], Instance/Rng/Polynomial.v *)

Fail Definition pt_eq_type_elim {K : RingObject}
  (s t : @PTerm K) (He : pt_eq s t) : @PTerm K :=
  ltac:(induction He; exact pt_x).

Fail Definition peval_type_elim (K S : RingObject) (phi : K ~{Rng}~> S)
  (x : carrier (rig_setoid S)) (t u : @PTerm K) (He : pt_eq t u) :
  peval phi x t ≈ peval phi x u :=
  ltac:(induction He).

Example pt_pequiv_control {K : RingObject} (s t : @PTerm K)
  (He : pt_eq s t) :
  @pequiv _ _ (rig_prop (PolyRing K)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example pt_respects_control (K S : RingObject) (phi : K ~{Rng}~> S)
  (x : carrier (rig_setoid S))
  (Kcomm : ∀ a b : carrier (rig_setoid K),
     rig_mul K a b ≈ rig_mul K b a)
  (Hcs : ∀ a : carrier (rig_setoid K),
     rig_mul S x (rig_map phi a) ≈ rig_mul S (rig_map phi a) x)
  (t u : @PTerm K) (He : pt_eq t u) :
  peval phi x t ≈ peval phi x u :=
  peval_respects K S phi x Kcomm Hcs t u He.

(** ** 4. [tt_eq], Instance/Vect/TensorAlgebra.v *)

Fail Definition tt_eq_type_elim {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : tt_eq s t) : TTerm V :=
  ltac:(induction He; exact (tt_scal (rig_zero (`1 K)))).

Fail Definition teval_type_elim (K : CRng) (V : RModObject (`1 K))
  (A : AAlgObject K) (f : AAlgLinear V A) (s t : TTerm V)
  (He : tt_eq s t) : teval A f s ≈ teval A f t :=
  ltac:(induction He).

Example tt_pequiv_control {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : tt_eq s t) :
  @pequiv _ _ (rig_prop (TensorRing V)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example tt_respects_control (K : CRng) (V : RModObject (`1 K))
  (A : AAlgObject K) (f : AAlgLinear V A) (s t : TTerm V)
  (He : tt_eq s t) : teval A f s ≈ teval A f t :=
  teval_respects K V A f s t He.

(** ** 5. [et_eq], Instance/Vect/TensorAlgebra.v

    Moved in LOCKSTEP with [tt_eq]: [ee_base] embeds a whole [tt_eq], so the
    exterior relation could not stay in [Type] over a [Prop]-valued tensor
    relation and still make Λ(V) a quotient of T(V). *)

Fail Definition et_eq_type_elim {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : et_eq s t) : TTerm V :=
  ltac:(induction He; exact (tt_scal (rig_zero (`1 K)))).

Example et_pequiv_control {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : et_eq s t) :
  @pequiv _ _ (rig_prop (ExtRing V)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example et_respects_control (K : CRng) (V : RModObject (`1 K))
  (A : AAlgObject K) (f : AltLinear V A) (s t : TTerm V)
  (He : et_eq s t) : teval A (alt_lin f) s ≈ teval A (alt_lin f) t :=
  exteval_respects K V A f s t He.

(** ** 6. [uenv_eq], Adjunction/Enveloping.v *)

Fail Definition uenv_eq_type_elim {K : CRng} {L : LieObject K}
  (s t : UEnvTerm L) (He : uenv_eq s t) : UEnvTerm L :=
  ltac:(induction He; exact (uen_scal (rig_zero (`1 K)))).

Example uenv_pequiv_control {K : CRng} {L : LieObject K}
  (s t : UEnvTerm L) (He : uenv_eq s t) :
  @pequiv _ _ (rig_prop (UEnvRing L)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example uenv_respects_control (K : CRng) (L : LieObject K)
  (A : AAlgObject K) (f : LieHom L (lie_of_aalg A)) (s t : UEnvTerm L)
  (He : uenv_eq s t) : uenv_eval A f s ≈ uenv_eval A f t :=
  uenv_eval_respects K L A f s t He.

(*
   本节说明 ProbeTermModelPropRng 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* NEGATIVE 7a.  The witness cannot be read back out. *)
Fail Definition rquot_rel_type_elim {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) (H : rquot_rel I x y) :
  idl_mem I (ab_sub (ring_ab R) x y) :=
  ltac:(destruct H as [K]; exact K).

(* NEGATIVE 7b.  The biconditional is NOT available against the bare
   membership; it holds only up to the truncation. *)
Fail Definition rquot_zero_iff_untruncated {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  rquot_rel I x (rig_zero R) ↔ idl_mem I x :=
  rquot_rel_zero_iff I x.

(* CONTROL.  The direction that loses nothing keeps its [Type]-valued
   hypothesis. *)
Example rquot_of_mem_control {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) (Hx : idl_mem I x) :
  rquot_rel I x (rig_zero R) := rquot_rel_of_mem I x Hx.

(* CONTROL.  The truncated biconditional, APPLIED. *)
Example rquot_zero_iff_control {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  rquot_rel I x (rig_zero R) ↔ inhabited (idl_mem I x) :=
  rquot_rel_zero_iff I x.

(* CONTROL.  The quotient's `≈` IS [rquot_rel], and is its own [Prop]
   mirror. *)
Example rquot_pequiv_control {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) (H : rquot_rel I x y) :
  @pequiv _ _ (rig_prop (QuotientRing I)) x y := H.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example lquot_is_rquot_control {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y := eq_refl.

(** ** Instrument check, scope-free *)

Fail Example probe_term_model_rng_instrument : true = false := eq_refl.
