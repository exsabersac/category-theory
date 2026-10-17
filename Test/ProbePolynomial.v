(*
   本文件为测试：ProbePolynomial。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
Require Import Category.Instance.Rng.Pointed.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
   本节说明 ProbePolynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example probe_instrument (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (@poly_x K) = s := eq_refl.

(** ** (1) Addition and multiplication compute; zero and one do not *)

(* POSITIVE CONTROLS. *)

Example probe_extend_add (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s)
  (t u : @PTerm K) :
  rig_map (poly_extend phi s Kc Hc) (rig_add (PolyRing K) t u)
    = rig_add S (rig_map (poly_extend phi s Kc Hc) t)
                (rig_map (poly_extend phi s Kc Hc) u) := eq_refl.

Example probe_extend_mul (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s)
  (t u : @PTerm K) :
  rig_map (poly_extend phi s Kc Hc) (rig_mul (PolyRing K) t u)
    = rig_mul S (rig_map (poly_extend phi s Kc Hc) t)
                (rig_map (poly_extend phi s Kc Hc) u) := eq_refl.

(*
   本节说明 ProbePolynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_extend_zero_not_eq_refl
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_zero (PolyRing K))
    = rig_zero S := eq_refl.

Fail Example probe_extend_one_not_eq_refl
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_one (PolyRing K))
    = rig_one S := eq_refl.

(* ... and both DO hold up to [≈], which is what the file claims. *)

Example probe_extend_zero_up_to_equiv
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_zero (PolyRing K)) ≈ rig_zero S.
Proof. exact (rig_map_zero (poly_extend phi s Kc Hc)). Qed.

(* The ℤ instance behaves the OTHER way, which is why the probes above
   are stated at a variable ring: [zring S 0] reduces to [rig_zero S]. *)

Example probe_zpoly_zero_does_compute :
  rig_map (zpoly_eval Int_Ring 3%Z) (rig_zero ZPoly) = rig_zero Int_Ring
  := eq_refl.

(** ** (2) The backward transpose does not compute *)

(*
   本节说明 ProbePolynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_transpose_not_eq_refl (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    = peval (`1 h) (`2 Q) t := eq_refl.

(* POSITIVE CONTROL: the same statement up to [≈] is a theorem. *)

Example probe_transpose_up_to_equiv (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    ≈ peval (`1 h) (`2 Q) t.
Proof. exact (poly_pointed_adj_transpose_evaluates A Q h t). Qed.

(** ** (3) The free object, its point, the arrow and the unit do compute *)

Example probe_free_object (A : CRng) : PolyPointed A = PolyPt A := eq_refl.

Example probe_free_point (A : CRng) :
  `2 (PolyPointed A) = @poly_x (`1 A) := eq_refl.

Example probe_universal_arrow (A : CRng) :
  @arrow _ _ A CRngPt_Forget (poly_pointed_universal_arrow A)
    = poly_pointed_arrow A := eq_refl.

Example probe_unit (A : CRng) (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (poly_pointed_unit A)) c = @pt_const (`1 A) c := eq_refl.

(*
   本节说明 ProbePolynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_unit_not_the_arrow (A : CRng) :
  poly_pointed_unit A = poly_pointed_arrow A := eq_refl.

(* POSITIVE CONTROL for that negative: the two ARE equal as morphisms of
   [CRng], which is an equation up to [≈] and holds. *)

Example probe_unit_equiv_arrow (A : CRng) :
  poly_pointed_unit A ≈ poly_pointed_arrow A.
Proof. intro c; reflexivity. Qed.

(*
   本节说明 ProbePolynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example probe_universal_element_is_x :
  @aue_elem Rng Rng_Forget ZPoly zpoly_universal_element = @poly_x Int_Ring
  := eq_refl.

Example probe_x_is_not_zero :
  (@poly_x Int_Ring ≈ rig_zero ZPoly) → False.
Proof. exact zpoly_x_nonzero. Qed.
