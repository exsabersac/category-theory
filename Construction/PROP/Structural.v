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

(* * * Structural isomorphisms for the free PROP / * * 自由PROP的结构同构 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/associator
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/Coherence_condition

 Package the three structural maps of a monoidal category — left
 unitor, right unitor, associator — as isomorphisms in [FreeCat S]
 using [T_cast].

 “Structural” here is the monoidal-coherence sense (the unitors and
 associator of nLab/Mac Lane), not the permutation sense: a PROP also
 has the symmetric structural maps [S_n ⊆ PROP(n,n)] built from braids
 and identities (see [T_swap] in Term.v), which are a separate family.

 The arity-equations are pure [Nat] facts:

 [Nat.add_0_l n]       : 0 + n = n                  (left unit)
 [Nat.add_0_r n]       : n + 0 = n                  (right unit)
 [Nat.add_assoc x y z] : x + (y + z) = (x + y) + z  (associator)

 Because [Nat.add] is left-strict in Coq, the left unitor at
 [0 + n] is the identity definitionally; the right unitor and the
 associator require non-trivial casts. 

 --------
 nLab:  https://ncatlab.org/nlab/show/monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/associator 
 维基百科:  https://en.wikipedia.org/wiki/Monoidal_category 
 维基百科:  https://en.wikipedia.org/wiki/Coherence_condition 

 使用  [T_cast]  将单体范畴的三种结构映射——左幺元同构、右幺元同构、结合子——作为  [FreeCat S]  中的同构打包。

 这里的“结构”是单体相容性的意义（nLab/Mac Lane 的幺元同构和结合子），而不是置换意义：PROP 还有由编织和恒等映射构成的对称结构映射  [S_n ⊆ PROP(n,n)]  （见 Term.v 中的  [T_swap] ），它们是另一类。

 元数方程是纯粹的  [Nat]  事实：

 [Nat.add_0_l n]        : 0 + n = n                  (左幺元)
 [Nat.add_0_r n]       : n + 0 = n                  (右幺元)
 [Nat.add_assoc x y z]       : x + (y + z) = (x + y) + z  (结合子)因为 [Nat.add] 在 Coq 中是左严格的，所以在 [0 + n] 上的左单位元是定义上的恒等；右单位元和结合子则需要非平凡的类型转换。
*)

Open Scope nat_scope.

Section Structural.

Context (S : Signature).

(*
 Left unitor [0 + n ≅ n] in [FreeCat S].  Definitionally [0 + n = n],
 so the cast is along [eq_refl] and the unitor is the literal identity. 

 --------
 左单位元 [0 + n ≅ n] 在 [FreeCat S] 中。按照定义 [0 + n = n]，所以转换沿着 [eq_refl] 进行，单位元就是字面上的恒等式。
*)
Program Definition FreeCat_unit_left (n : nat) : @Isomorphism (FreeCat S) (0 + n) n := {|
  to   := T_cast (Nat.add_0_l n);
  from := T_cast (eq_sym (Nat.add_0_l n))
|}.
Next Obligation. apply T_cast_inv_sym. Qed.
Next Obligation. apply T_cast_inv. Qed.

(*
 Right unitor [n + 0 ≅ n] in [FreeCat S].  [Nat.add_0_r] is
 propositional, not definitional, so the cast is along a non-trivial
 equation. 

 --------
 在 [FreeCat S] 中的右单位元 [n + 0 ≅ n]。[Nat.add_0_r] 是命题的，而不是定义的，因此类型转换是沿着一个非平凡的方程进行的。
*)
Program Definition FreeCat_unit_right (n : nat) : @Isomorphism (FreeCat S) (n + 0) n := {|
  to   := T_cast (Nat.add_0_r n);
  from := T_cast (eq_sym (Nat.add_0_r n))
|}.
Next Obligation. apply T_cast_inv_sym. Qed.
Next Obligation. apply T_cast_inv. Qed.

(*
 Associator [(x + y) + z ≅ x + (y + z)] in [FreeCat S].  Likewise
 propositional via [Nat.add_assoc].  Oriented [to : (x+y)+z ~> x+(y+z)],
 matching the nLab associator α : (A⊗B)⊗C → A⊗(B⊗C). 

 --------
 在 [FreeCat S] 中的结合子 [(x + y) + z ≅ x + (y + z)]。同样，通过 [Nat.add_assoc] 的命题方式。定向 [to : (x+y)+z ~> x+(y+z)]，与 nLab 结合子 α : (A⊗B)⊗C → A⊗(B⊗C) 匹配。
*)
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
