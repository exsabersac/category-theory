Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.

From Coq Require Import Arith.

Generalizable All Variables.

(*
   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CastTensor.

Context (S : Signature).

Open Scope nat_scope.

(*
   本节说明 CastTensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma T_tens_id_cast_left {m a b : nat} (e : a = b) :
  TermEq S (T_tens (T_id m) (T_cast e))
           (T_cast (f_equal (fun k => m + k) e)).
Proof.
  destruct e.
  cbn.
  apply TE_tens_id.
Qed.

(** Symmetric variant: cast LEFT, 恒等 RIGHT. （已译） *)
Lemma T_tens_cast_id_right {a b n : nat} (e : a = b) :
  TermEq S (T_tens (T_cast e) (T_id n))
           (T_cast (f_equal (fun k => k + n) e)).
Proof.
  destruct e.
  cbn.
  apply TE_tens_id.
Qed.

(** Tensor preserves identities: [id_m ⊕ id_n ≈ id_(m+n)]. This is
 just primitive [TE_tens_id] constructor restated named
 引理 (no cast involved) use rewrite target. （已译） *)
Lemma T_tens_id_id (m n : nat) :
  TermEq S (T_tens (T_id m) (T_id n)) (T_id (m + n)).
Proof. apply TE_tens_id. Qed.

(* * Composing trivial [T_cast eq_refl] (which is [T_id]) onto a
 tensor is 恒等 operation. [T_cast eq_refl] reduces to
 [T_id (m1+m2)], so composite collapses left 恒等.（已译） *)
Lemma T_comp_cast_tens_left {m1 n1 m2 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_cast eq_refl) (T_tens f g))
           (T_tens f g).
Proof. cbn. apply TE_id_left. Qed.

(** Dual: post-composing a trivial [T_cast eq_refl] on the input side
    of a tensor collapses by right identity. *)
Lemma T_comp_tens_cast_right {m1 n1 m2 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_tens f g) (T_cast eq_refl))
           (T_tens f g).
Proof. cbn. apply TE_id_right. Qed.

End CastTensor.
