Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.

From Coq Require Import Arith.

Generalizable All Variables.

(*
   * * [T_cast] interaction with [T_tens]

   Bridge lemmas that the Monoidal instance on [FreeCat S]
   (Construction/PROP/Monoidal.v) uses to discharge naturality of the
   structural isomorphisms.
   [T_tens] mixes two arities additively; [T_cast] rewrites a single
   arity along a propositional equation.  The lemmas below all reduce
   the cast away by [destruct]-ing the arity equation, after which the
   goal is closed by a primitive tensor/identity constructor of
   [TermEq] ([TE_tens_id], [TE_id_left], or [TE_id_right]). 

   --------
   * *  [T_cast] 与 [T_tens] 的交互

   桥接引理是用于 [FreeCat S]（Construction/PROP/Monoidal.v）上的单体实例来处理结构同构的自然性。
   [T_tens] 按加法混合两个元数；[T_cast] 沿命题等式重写单个元数。下面的引理都通过 [destruct] -ing 元数等式来减少类型转换，之后目标由 [TermEq]（[TE_tens_id]、[TE_id_left] 或 [TE_id_right]）的原始张量/恒等构造器闭合。
*)

Section CastTensor.

Context (S : Signature).

Open Scope nat_scope.

(*
   * Tensoring an identity with a cast on the right factor equals a
   single cast along the [+]-congruenced arity equation.

   [(id_m ⊕ T_cast e) ≈ T_cast (f_equal (m + _) e)]

   The right-hand arity equation [m + a = m + b] is [e] congruenced by
   left-addition of [m]; at [eq_refl] it reduces to [eq_refl] and the
   goal becomes [TE_tens_id]. 

   --------
   * 将恒等映射与右因子的类型转换张量化等于沿着  [+] -同余元方程的单一类型转换。

   [(id_m ⊕ T_cast e) ≈ T_cast (f_equal (m + _) e)]

   右侧的元方程  [m + a = m + b]  通过左加  [m]  与  [e]  同余；在  [eq_refl]  它简化为  [eq_refl] ，目标变为  [TE_tens_id] 。
*)
Lemma T_tens_id_cast_left {m a b : nat} (e : a = b) :
  TermEq S (T_tens (T_id m) (T_cast e))
           (T_cast (f_equal (fun k => m + k) e)).
Proof.
  destruct e.
  cbn.
  apply TE_tens_id.
Qed.

(*
   * Symmetric variant: cast on the LEFT, identity on the RIGHT. 

   --------
   * 对称变体：在左侧进行投射，在右侧保持不变。
*)
Lemma T_tens_cast_id_right {a b n : nat} (e : a = b) :
  TermEq S (T_tens (T_cast e) (T_id n))
           (T_cast (f_equal (fun k => k + n) e)).
Proof.
  destruct e.
  cbn.
  apply TE_tens_id.
Qed.

(*
   * Tensor preserves identities: [id_m ⊕ id_n ≈ id_(m+n)].  This is
   just the primitive [TE_tens_id] constructor restated as a named
   lemma (no cast involved) for use as a rewrite target. 

   --------
   * 张量保持恒等式：[id_m ⊕ id_n ≈ id_(m+n)]。 这只是将原始的[TE_tens_id]构造函数以命名引理的形式重新表述（没有涉及类型转换），以便用作重写目标。
*)
Lemma T_tens_id_id (m n : nat) :
  TermEq S (T_tens (T_id m) (T_id n)) (T_id (m + n)).
Proof. apply TE_tens_id. Qed.

(*
   * Composing a trivial [T_cast eq_refl] (which is [T_id]) onto a
   tensor is the identity operation.  [T_cast eq_refl] reduces to
   [T_id (m1+m2)], so the composite collapses by left identity. 

   --------
   * 将一个平凡的 [T_cast eq_refl]（即 [T_id]）作用在张量上是恒等操作。[T_cast eq_refl] 简化为 [T_id (m1+m2)]，因此复合通过左恒等式塌缩。
*)
Lemma T_comp_cast_tens_left {m1 n1 m2 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_cast eq_refl) (T_tens f g))
           (T_tens f g).
Proof. cbn. apply TE_id_left. Qed.

(*
   * Dual: post-composing a trivial [T_cast eq_refl] on the input side
   of a tensor collapses by right identity. 

   --------
   * 双重：在张量的输入端对一个平凡的 [T_cast eq_refl] 进行后组合会通过右恒等式塌缩。
*)
Lemma T_comp_tens_cast_right {m1 n1 m2 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_tens f g) (T_cast eq_refl))
           (T_tens f g).
Proof. cbn. apply TE_id_right. Qed.

End CastTensor.
