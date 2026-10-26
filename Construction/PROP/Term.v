Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * Raw terms over a PROP signature / * * 在 PROP 签名上的原始项 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 nLab: https://ncatlab.org/nlab/show/string+diagram
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 The syntactic representation of morphisms in the free PROP on a
 signature [S].  A term of type [Term S m n] is a string-diagram
 expression with [m] input wires and [n] output wires, built up from:

 - identity wires [T_id n]
 - braids [T_braid m n] (the canonical “block braiding” that
 crosses an [m]-wide bundle past an [n]-wide bundle)
 - sequential composition [T_comp]
 - parallel composition (tensor) [T_tens]
 - signature-supplied generators [T_gen]

 This file defines just the SYNTAX — no equational theory.  The
 equational theory (associativity / unit / braid coherence /
 interchange) lives in a successor file [Construction/PROP/TermEq.v]
 and the full [FreePROP] category in [Construction/PROP/Free.v].

 The arity-indexing means [Term S] is naturally a “many-sorted on
 naturals” data structure: arities propagate up through sequential
 and parallel composition by the corresponding [Nat] operation. 

 --------
 nLab:  https://ncatlab.org/nlab/show/PROP 
 nLab:  https://ncatlab.org/nlab/show/symmetric+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/string+diagram 
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 自由 PROP 上的态射的语法表示在一个符号  [S]  中。类型为  [Term S m n]  的项是一个具有  [m] 个输入线和  [n] 个输出线的字符串图表达式，由以下部分构建：

 - 恒等线  [T_id n] 
 - 编织  [T_braid m n]  （规范的“块编织”，将一个宽为  [m] 的束穿过一个宽为  [n] 的束）
 - 顺序组合  [T_comp] 
 - 并行组合（张量）  [T_tens] 
 - 符号提供的生成元  [T_gen] 

 这个文件只定义了语法 — 没有方程理论。方程理论（结合律 / 单位 / 编织相容性 / 交换律）存在于后续文件  [Construction/PROP/TermEq.v] 
 中，以及完整的  [FreePROP] 类别在  [Construction/PROP/Free.v] 中。算子元数索引意味着 [Term S] 自然是一个“多排序的自然数”数据结构：元数通过顺序和并行组合按相应的 [Nat] 操作向上传播。
*)

Section Term.

Context (S : Signature).

Inductive Term : nat -> nat -> Type :=
  | T_id    : forall n, Term n n                    (* identity on n wires / n 条导线上的身份 *)
  | T_braid : forall m n, Term (m + n) (n + m)      (* symmetry σ_{m,n} / 对称 σ_{m,n} *)
  | T_comp  : forall {m n p}, Term n p -> Term m n -> Term m p
                                                    (* g ⊙ f : m ⇒ p (g outer) / g ⊙ f : m ⇒ p（g 外部） *)
  | T_tens  : forall {m1 n1 m2 n2},                 (* parallel: arities add / 并行：元数相加 *)
              Term m1 n1 -> Term m2 n2 -> Term (m1 + m2) (n1 + n2)
  | T_gen   : forall {m n}, S m n -> Term m n.      (* signature generator / 签名生成器 *)

End Term.

Arguments T_id    {S} n.
Arguments T_braid {S} m n.
Arguments T_comp  {S m n p} _ _.
Arguments T_tens  {S m1 n1 m2 n2} _ _.
Arguments T_gen   {S m n} _.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "f ⊙t g" := (T_comp f g) (at level 40, left associativity) : term_scope.
Notation "f ⊕t g" := (T_tens f g) (at level 30, right associativity) : term_scope.

(** ** Smart constructors / ** 智能构造函数 *)

(** The “swap” braid on two single wires. / 两条单根导线上的“交换”编织。 *)
Definition T_swap {S : Signature} : Term S 2 2 :=
  T_braid 1 1.

(*
 Relabel a whole term along a signature embedding [inc : SubSig S T],
 recursing through the structural constructors and remapping each
 [T_gen] leaf.  Arities [m n] are preserved, so this is the action on
 morphisms of the induced functor [FreePROP S -> FreePROP T]. 

 --------
 沿着签名嵌入 [inc : SubSig S T] 重新标记整个项，递归遍历结构构造器并重新映射每个 [T_gen] 叶子。保留 [m n] 的元数，因此这是诱导函子 [FreePROP S -> FreePROP T] 在态射上的作用。
*)
Definition T_inj {S T : Signature} (inc : SubSig S T)
                 {m n : nat} (t : Term S m n) : Term T m n.
Proof.
  induction t.
  - exact (T_id _).
  - exact (T_braid _ _).
  - exact (T_comp IHt1 IHt2).
  - exact (T_tens IHt1 IHt2).
  - exact (T_gen (inc _ _ s)).
Defined.

(** ** Examples / ** 示例 *)

(** Identity on a single wire. / 单线身份。 *)
Definition wire {S : Signature} : Term S 1 1 := T_id 1.

(** Identity on two wires in parallel. / 在两根并联电线上识别身份。 *)
Definition wire2 {S : Signature} : Term S 2 2 := T_id 2.

(** The empty term: 0-input, 0-output. / 空项：0 输入，0 输出。 *)
Definition T_nothing {S : Signature} : Term S 0 0 := T_id 0.
