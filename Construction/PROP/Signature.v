Require Import Category.Lib.

From Coq Require Import Arith.

Generalizable All Variables.

(*
   * * Signatures over PROPs

   A SIGNATURE is the data of a (one-sorted) symmetric monoidal
   theory: a family of typed generators indexed by their input/output
   arity.  Unlike an ordinary algebraic (Lawvere) theory, whose
   operations have a single output, a generator here may have any
   output coarity, so a signature is just the underlying object of
   the free-PROP adjunction, an element of [Set^(nat x nat)] (here in
   [Type]).  This is the standard "many-sorted signature in the
   arities-are-naturals setting" that PROPs are designed to capture
   syntactically.

   Concretely [Sig m n] is the [Type] of generator names that have
   [m] input wires (the domain/arity) and [n] output wires (the
   codomain/coarity).  In examples:

   - The empty signature [Empty_Sig m n := Empty_set] presents a
   PROP with NO non-structural generators (just identity,
   composition, tensor, braid).  Its free PROP on no generators
   is the permutation category: morphisms [m ~> n] are empty
   unless [m = n], in which case they are the braidings of [m]
   wires.  (NB: the free *hypergraph* PROP on no generators, which
   additionally quotients by the special-commutative-Frobenius
   axioms, is the PROP of cospans of finite sets; that extra
   structure is NOT imposed by the [FreePROP] of this development,
   which quotients only by the strict-SMC axioms.)
   - The commutative-monoid signature has one [Sig 2 1] (mul) and
   one [Sig 0 1] (unit).  Its free PROP-on-signature with the
   commutative-monoid equational theory is the PROP of finite
   sets and functions (i.e. FinSet, the prop for commutative
   monoids; multivalued/span semantics would instead require the
   comonoid generators of a bicommutative bimonoid).
   - For an electrical-circuit signature one might have [Sig 0 1]
   for a battery, [Sig 1 1] for a resistor, [Sig 2 1] for a
   Y-junction, etc.

   The signature is the INPUT to free-PROP constructions: given [S],
   [FreePROP S] is the strict symmetric monoidal category whose
   morphisms are [S]-labelled string diagrams modulo the
   strict-SMC axioms.  This file defines just [Signature]; the
   [Term] inductive and the [FreePROP] construction live in
   [Construction/PROP/Free.v] and successor files. 

   --------
   * * PROPs 上的符号

   符号（SIGNATURE）是（单排序）对称幺半范畴理论的数据：一个按输入/输出元数索引的类型化生成元族。与普通的代数（Lawvere）理论不同，后者的运算只有单一输出，这里的生成元可以有任意输出共元数，因此符号只是自由 PROP 对偶下的基础对象，是 [Set^(nat x nat)] 中的一个元素（这里在 [Type] 中）。这是 PROPs 设计用来在句法上捕捉的标准“多排序符号（自然数作为元数的设置）”。

   具体来说，[Sig m n] 是具有 [m] 个输入线（域/元数）和 [n] 个输出线（余域/共元数）的生成元名称的 [Type]。在例子中：- 空签名 [Empty_Sig m n := Empty_set] 提供了一个没有非结构生成元的 PROP（只有恒等、组合、张量、编织）。它在没有生成元的情况下的自由 PROP 是排列范畴：态射 [m ~> n] 为空，除非 [m = n]，此时它们是 [m] 根的编织。（注意：在没有生成元的情况下，自由*超图*PROP，额外通过特殊交换 Frobenius 公理取商，是有限集的余跨范畴；而本开发中的 [FreePROP] 只通过严格 SMC 公理取商，并没有施加那额外结构。）
   - 交换单元签名具有一个 [Sig 2 1]（乘法）和一个 [Sig 0 1]（单位）。其自由 PROP-符号与交换幺半群方程理论一起，是有限集合与函数的 PROP（即 FinSet，交换幺半群的 PROP；多值/跨度语义则需要双交换双半群的余单元生成元）。- 对于电路符号，电池可能用 [Sig 0 1]，电阻用 [Sig 1 1]，Y 型结点用 [Sig 2 1]，等等。

   符号是自由 PROP 构造的输入：给定 [S]，[FreePROP S] 是严格对称单体范畴，其态射是 [S] 标记的弦图，模严格 SMC 公理。该文件仅定义 [Signature]；[Term] 归纳和 [FreePROP] 构造存在于 [Construction/PROP/Free.v] 及后续文件中。
*)

Definition Signature : Type := nat -> nat -> Type.

(** ** Examples / ** 示例 *)

(*
   * The empty signature.  Useful as a base case: [FreePROP Empty_Sig]
   is the PROP whose morphisms are exactly the strict-SMC syntactic
   rearrangements (identity, composition, tensor, braid) — the free
   PROP on no generators. 

   --------
   * 空签名。作为基本情况很有用：[FreePROP Empty_Sig]  
   是一个 PROP，其态射正好是严格 SMC 的句法重排（恒等、合成、张量、编织）——即没有生成元的自由 PROP。
*)
Definition Empty_Sig : Signature :=
  fun (_ _ : nat) => Empty_set.

(*
   * The signature of a single generator [g : m -> n] (with [m] inputs
   and [n] outputs), with no other generators.  The generator's arity
   [(m, n)] is arbitrary, not fixed to a binary operation: [Sig a b]
   is [unit] exactly when [(a, b) = (m, n)] and [Empty_set] otherwise.
   Parameterised over the input and output arities
   so the same skeleton can present a Y-junction (2, 1), a fork (1, 2),
   a unit (0, 1), and so on. 

   --------
   * 单个生成元 [g : m -> n] 的签名（具有 [m] 个输入和 [n] 个输出），且没有其他生成元。生成元的元数 [(m, n)] 是任意的，并不固定为二元操作：[Sig a b] 当 [(a, b) = (m, n)] 时为 [unit]，否则为 [Empty_set]。根据输入和输出的元数参数化，因此相同的骨架可以表示 Y 型连接（2, 1）、分叉（1, 2）、单位（0, 1）等等。
*)
Definition Single_Sig (m n : nat) : Signature :=
  fun a b => if Nat.eqb a m
             then if Nat.eqb b n then unit else Empty_set
             else Empty_set.

(*
   * ** Operations on signatures

   Sum (disjoint union) of two signatures: a generator is a generator
   of one or the other.  This lets you build complex signatures from
   smaller ones — e.g. the commutative-monoid signature is the sum of
   [Single_Sig 2 1] (multiplication) and [Single_Sig 0 1] (unit). 

   --------
   * ** 签名的操作

   两个签名的和（不相交并集）：一个生成元是其中一个签名的生成元。  
   这使你可以从较小的签名构建复杂签名——例如，交换幺半群签名是  
   [Single_Sig 2 1]（乘法）和 [Single_Sig 0 1]（单位元）的和。
*)
Definition Sum_Sig (S T : Signature) : Signature :=
  fun m n => sum (S m n) (T m n).

(*
   * Sub-signature: an arity-preserving family of generator
   relabellings into another signature — despite the name, no
   injectivity is required (generator collapses are allowed).
   Inhabited by [inl] / [inr] / nested projection chains. 

   --------
   * 子签名：一种保持元数的生成器重标记族，用于转换到另一个签名——尽管名称如此，并不要求单射性（允许生成器折叠）。  
   由 [inl] / [inr] / 嵌套投影链构成。
*)
Definition SubSig (Sub Sup : Signature) : Type :=
  forall m n, Sub m n -> Sup m n.

(** The identity sub-signature. / 身份子签名。 *)
Definition SubSig_id (S : Signature) : SubSig S S :=
  fun _ _ s => s.

(** Sub-signature composition. / 子签名组成。 *)
Definition SubSig_compose {S T U : Signature}
  (f : SubSig T U) (g : SubSig S T) : SubSig S U :=
  fun m n s => f m n (g m n s).
