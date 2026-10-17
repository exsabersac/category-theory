Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Cast.

From Coq Require Import Arith.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/associator
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Coherence_condition

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Open Scope nat_scope.

Section Structural.

Context (S : Signature).

(* Left unitor [0 + n ≅ n] [FreeCat S]. Definitionally [0 + n = n],
 so cast along [eq_refl] unitor literal 恒等. （已译） *)
Program Definition FreeCat_unit_left (n : nat) : @Isomorphism (FreeCat S) (0 + n) n := {|
  to   := T_cast (Nat.add_0_l n);
  from := T_cast (eq_sym (Nat.add_0_l n))
|}.
Next Obligation. apply T_cast_inv_sym. Qed.
Next Obligation. apply T_cast_inv. Qed.

(* Right unitor [n + 0 ≅ n] in [FreeCat S].  [Nat.add_0_r] is
   propositional, not definitional, so the cast is along a non-trivial
   equation. *)
Program Definition FreeCat_unit_right (n : nat) : @Isomorphism (FreeCat S) (n + 0) n := {|
  to   := T_cast (Nat.add_0_r n);
  from := T_cast (eq_sym (Nat.add_0_r n))
|}.
Next Obligation. apply T_cast_inv_sym. Qed.
Next Obligation. apply T_cast_inv. Qed.

(* Associator [(x + y) + z ≅ x + (y + z)] in [FreeCat S].  Likewise
   propositional via [Nat.add_assoc].  Oriented [to : (x+y)+z ~> x+(y+z)],
   matching the nLab associator α : (A⊗B)⊗C → A⊗(B⊗C). *)
Program Definition FreeCat_tensor_assoc (x y z : nat)
  : @Isomorphism (FreeCat S) ((x + y) + z) (x + (y + z)) := {|
  to   := T_cast (eq_sym (Nat.add_assoc x y z));
  from := T_cast (Nat.add_assoc x y z)
|}.
Next Obligation. apply T_cast_inv. Qed.
Next Obligation. apply T_cast_inv_sym. Qed.

End Structural.

Close Scope nat_scope.

Arguments FreeCat_unit_left  S n : assert.
Arguments FreeCat_unit_right S n : assert.
Arguments FreeCat_tensor_assoc S x y z : assert.
