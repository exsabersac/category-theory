Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * The free PROP category on a signature / * * 签名上的免费PROP类别 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Free_category

 A PROP is a strict symmetric monoidal category whose objects are the
 natural numbers and whose tensor on objects is addition, [m ⊗ n = m + n].
 The free PROP on a signature [S] has as its [m ~> n] arrows the [S]-terms
 [Term S m n] quotiented by the laws of a symmetric monoidal category; this
 is the standard "free = syntactic" construction, the symmetric-monoidal
 analogue of the path/quotient construction of a free category.

 This file assembles only the underlying [Category] layer of that quotient:

 - obj      := nat                         (objects are ℕ)
 - hom m n  := Term S m n  modulo  TermEq  (string-diagram terms / ≈)
 - id       := T_id                        (identity wires)
 - compose  := T_comp                      (sequential composition)

 The hom-equivalence ≈ is [TermEq S], so the [Category] laws (left/right
 unit, associativity) are exactly its [TE_id_left] / [TE_id_right] /
 [TE_assoc] constructors, and [compose_respects] is its [TE_comp_cong]
 congruence.  The [Monoidal], [SymmetricMonoidal], [StrictMonoidal], and
 [PROP] instances — which complete [FreeCat S] to a free strict
 symmetric monoidal category — live in the successor files: on top of
 the tensor functor ([Construction/PROP/Tensor.v]), the structural
 isomorphisms ([Construction/PROP/Structural.v]) and their naturality
 lemmas ([Construction/PROP/Naturality.v]), the shared monoidal record
 is built in [Construction/PROP/Monoidal.v], its braided/symmetric/
 strict structure in [Construction/PROP/Braided.v] / [Symmetric.v] /
 [Strict.v], and the bundled [FreePROP S : PROP] — with definitional
 coherence — in [Construction/PROP/Instance.v]; interpretation and the
 universal property follow in [Interp.v] and [Universal.v]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/PROP 
 nLab:  https://ncatlab.org/nlab/show/free+category 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 
 维基百科:  https://en.wikipedia.org/wiki/Free_category 

 PROP 是一个严格的对称单体范畴，其对象是自然数，并且对象上的张量是加法，[m ⊗ n = m + n]。
 在签名 [S] 上的自由 PROP，其 [m ~> n] 箭头是 [S] 项 [Term S m n] ，按对称单体范畴的规律取商；
 这是标准的“自由 = 句法”构造，是自由范畴路径/商构造的对称单体类似物。

 本文件仅汇集了该商的底层 [Category] 层:- obj      := nat                         （对象是 ℕ）
 - hom m n  := Term S m n  模块 TermEq  （字符串图项 / ≈）
 - id       := T_id                        （恒等线）
 - compose  := T_comp                      （顺序组合）同伦等价 ≈ 是 [TermEq S]，因此 [Category] 公理（左/右单位，结合律）正是它的 [TE_id_left] / [TE_id_right] / [TE_assoc] 构造器，而 [compose_respects] 是它的 [TE_comp_cong] 合同。[Monoidal]、[SymmetricMonoidal]、[StrictMonoidal] 和 [PROP] 实例——它们将 [FreeCat S] 完成为自由严格对称单范畴——位于后续文件：在张量函子（[Construction/PROP/Tensor.v]）、结构同构（[Construction/PROP/Structural.v]）及其自然性引理（[Construction/PROP/Naturality.v]）之上，构建共享的单范畴记录在 [Construction/PROP/Monoidal.v]，其编织/对称/严格结构在 [Construction/PROP/Braided.v] / [Symmetric.v] / [Strict.v] 中，捆绑的 [FreePROP S : PROP]——具有定义性一致性——在 [Construction/PROP/Instance.v] 中；解释和普遍性质在 [Interp.v] 和 [Universal.v] 中跟进。
*)

Section FreeCategory.

Context (S : Signature).

(*
   * The hom-setoid: terms are quotiented by [TermEq]. 

   --------
   * Hom-集合：术语按 [TermEq] 进行等价类化。
*)
#[export] Program Instance Term_Setoid {m n : nat} : Setoid (Term S m n) := {|
  equiv := @TermEq S m n
|}.
Next Obligation.
  constructor.
  - intros t; apply TE_refl.
  - intros s t; apply TE_sym.
  - intros s t u; apply TE_trans.
Defined.

(*
   * Composition is the [T_comp] constructor; it respects [TermEq] by
   [TE_comp_cong]. 

   --------
   * 组合是 [T_comp] 构造函数；它通过 [TE_comp_cong] 尊重 [TermEq]。
*)
#[export] Program Instance T_comp_respects {m n p : nat} :
  Proper (equiv ==> equiv ==> equiv) (@T_comp S m n p).
Next Obligation.
  proper.
  apply TE_comp_cong; assumption.
Qed.

(*
   * Tensor (parallel composition) is also Proper for [TermEq], by
   [TE_tens_cong].  Allows [rewrite] under [T_tens]. 

   --------
   * 张量（并行组合）对于 [TermEq] 来说也是 Proper，由 [TE_tens_cong] 给出。允许 [rewrite] 在 [T_tens] 下。
*)
#[export] Program Instance T_tens_respects {m1 n1 m2 n2 : nat} :
  Proper (equiv ==> equiv ==> equiv) (@T_tens S m1 n1 m2 n2).
Next Obligation.
  proper.
  apply TE_tens_cong; assumption.
Qed.

(** The free category on [S]. / 在 [S] 上的免费分类。 *)
Program Definition FreeCat : Category := {|
  obj      := nat;
  hom      := @Term S;
  homset   := @Term_Setoid;
  id       := T_id;
  compose  := @T_comp S;
  compose_respects := @T_comp_respects;
  id_left  := fun m n f => TE_id_left f;
  id_right := fun m n f => TE_id_right f;
  comp_assoc := fun m n p q f g h => TE_sym _ _ (TE_assoc f g h);
  comp_assoc_sym := fun m n p q f g h => TE_assoc f g h
|}.

End FreeCategory.

Arguments FreeCat S : assert.
Arguments T_comp_respects {S m n p}.
