Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.CastTensor.

From Coq Require Import Arith.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Naturality.

Context (S : Signature).

Open Scope nat_scope.

(* * ** Left-unitor 自然性

 Goal (in [FreeCat S]):
 g ⊙ unit_left ≈ unit_left ⊙ bimap id g
 expanded [Term]:
 g ⊙ T_cast (Nat.add_0_l x) ≈ T_cast (Nat.add_0_l y) ⊙ (T_id 0 ⊕ g) （已译） *)

Lemma left_unit_natural {x y : nat} (g : Term S x y) :
  TermEq S (T_comp g (T_cast (Nat.add_0_l x)))
           (T_comp (T_cast (Nat.add_0_l y)) (T_tens (T_id 0) g)).
Proof.
  (* [Nat.add_0_l n : 0+n = n] is opaque, but by UIP on [nat] (which
     has decidable equality), every such cast equals [T_cast eq_refl]
     = [T_id n] via [T_cast_id]. *)
  rewrite (T_cast_id (Nat.add_0_l x)).
  rewrite (T_cast_id (Nat.add_0_l y)).
  apply TE_trans with g.
  - apply TE_id_right.
  - apply TE_sym.
    apply TE_trans with (T_tens (T_id 0) g).
    + apply TE_id_left.
    + apply TE_tens_id0_left.
Qed.

(* * ** Left-unitor 自然性, [from]-direction

 Goal: bimap id g ⊙ unit_left⁻¹ ≈ unit_left⁻¹ ⊙ g
 expanded:
 (T_id 0 ⊕ g) ⊙ T_cast (eq_sym (Nat.add_0_l x))
 ≈ T_cast (eq_sym (Nat.add_0_l y)) ⊙ g （已译） *)

Lemma left_unit_natural_from {x y : nat} (g : Term S x y) :
  TermEq S (T_comp (T_tens (T_id 0) g) (T_cast (eq_sym (Nat.add_0_l x))))
           (T_comp (T_cast (eq_sym (Nat.add_0_l y))) g).
Proof.
  rewrite (T_cast_id (eq_sym (Nat.add_0_l x))).
  rewrite (T_cast_id (eq_sym (Nat.add_0_l y))).
  apply TE_trans with (T_tens (T_id 0) g).
  - apply TE_id_right.
  - apply TE_trans with g.
    + apply TE_tens_id0_left.
    + apply TE_sym, TE_id_left.
Qed.

(* 相关说明。 （已译） *)

(** Tensoring two 恒等 terms [T_id 0] left collapses
 single 恒等 term. （已译） *)
Lemma tens_id0_id (n : nat) :
  TermEq S (T_tens (T_id 0) (T_id n)) (T_id n).
Proof. apply TE_tens_id0_left. Qed.

(** Repeated tensor of [T_id 0] on the left is still [T_id 0]. *)
Lemma tens_id0_id0 :
  TermEq S (T_tens (T_id 0) (T_id 0)) (T_id 0).
Proof. apply TE_tens_id0_left. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Naturality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma tens_id0_right_at_0 (f : Term S 0 0) :
  TermEq S (T_tens f (T_id 0)) f.
Proof.
  pose proof (TE_tens_id0_right f) as Hr.
  simpl in Hr.
  (* [Nat.add_0_r 0] reduces by [cbn]/[simpl] to [eq_refl] only if
     [Nat.add_0_r] is transparent.  In stdlib it is opaque, so we
     need to rewrite via UIP. *)
  unfold eq_rect_r in Hr; simpl in Hr.
  rewrite (Eqdep_dec.UIP_dec PeanoNat.Nat.eq_dec
            (Nat.add_0_r 0) eq_refl) in Hr.
  simpl in Hr.
  exact Hr.
Qed.

(* 相关说明。 （已译） *)

Lemma tens_id0_right_at (n : nat) (f : Term S n n) :
  TermEq S
    (eq_rect (n + 0) (fun k => Term S (n + 0) k)
             (T_tens f (T_id 0)) n (Nat.add_0_r n))
    (eq_rect_r (fun k => Term S k n) f (Nat.add_0_r n)).
Proof. exact (TE_tens_id0_right f). Qed.

(* 相关说明。 （已译） *)

Lemma tens_assoc_at {m1 n1 m2 n2 m3 n3 : nat}
                    (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3) :
  TermEq S
    (eq_rect (Nat.add (Nat.add n1 n2) n3)
             (fun k => Term S (Nat.add (Nat.add m1 m2) m3) k)
             (T_tens (T_tens f g) h)
             (Nat.add n1 (Nat.add n2 n3))
             (eq_sym (Nat.add_assoc n1 n2 n3)))
    (eq_rect_r
       (fun k => Term S k (Nat.add n1 (Nat.add n2 n3)))
       (T_tens f (T_tens g h))
       (eq_sym (Nat.add_assoc m1 m2 m3))).
Proof. exact (TE_tens_assoc f g h). Qed.

(*
   本节说明 Naturality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma braid_natural {m1 n1 m2 n2 : nat}
                    (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_tens g f) (T_braid m1 m2))
           (T_comp (T_braid n1 n2) (T_tens f g)).
Proof. apply TE_braid_natural. Qed.

(*
   本节说明 Naturality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma braid_invol (m n : nat) :
  TermEq S (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n)).
Proof. apply TE_braid_invol. Qed.

End Naturality.
