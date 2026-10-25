From Coq Require Import Utf8.
From Coq Require Import Program.

(*
   * * Proof automation for the intrinsically-typed de Bruijn STLC.

   This module collects the general-purpose tactics shared across the
   [Instance.Lambda] development.  Because terms, values and the reduction
   relations are all indexed by typing contexts and types, proofs constantly
   produce heterogeneous ([JMeq], notation [~=]) equalities between
   differently-typed objects and equalities between dependent pairs
   ([existT]); these tactics discharge that bookkeeping so that proof scripts
   can focus on the operational content.  [Program] is imported for
   [inj_pair2] (injectivity of [existT] up to UIP, from [Coq.Logic.Eqdep]). 

   --------
   * * 内在类型 de Bruijn STLC 的证明自动化。

   该模块收集了 [Instance.Lambda] 开发中共享的通用策略。由于项、值和归约关系都由类型上下文和类型索引，因此证明过程中会不断产生不同类型对象之间的异构（[JMeq]，符号 [~=]）等式以及依赖对之间的等式（[existT]）；这些策略处理这些繁琐的工作，从而使证明脚本可以专注于操作内容。[Program] 被导入用于 [inj_pair2]（[existT] 的可注入性直到 UIP，由 [Coq.Logic.Eqdep] 提供）。
*)

(* The [~=] (JMeq) notation is flagged deprecated by recent Rocq; silence the warning locally since it is pervasive in the dependently-typed goals below. / 最近的 Rocq 将 [~=]（JMeq）符号标记为已废弃；由于它在下面的依赖类型目标中广泛存在，请在本地静默该警告。 *)
Local Set Warnings "-deprecated-notation".

(*
 [reduce_jmeq] specialises induction hypotheses (and other quantified
 premises) of the shape
 ∀ x .., a = b → p ~= q → .. → Goal
 by supplying the witnesses and discharging each side-condition with the
 reflexive proof [eq_refl] / [JMeq_refl].  Such hypotheses arise from
 [dependent induction] / [dependent destruction]: the equality premises
 record how the indices of the eliminated term match those at the recursive
 call, and at each use site they hold definitionally.  The match is unrolled
 for one to four trailing [~=] premises, optionally preceded by three
 implicit arguments and one homogeneous [=] premise, covering the arities
 that actually occur in this development. 

 --------
 [reduce_jmeq] 专门处理形如 ∀ x .., a = b → p ~= q → .. → Goal 的归纳假设（以及其他量化前提），通过提供见证并使用反身性证明 [eq_refl] / [JMeq_refl] 来解决每个侧条件。这类假设来源于 [dependent induction] / [dependent destruction]：等式前提记录了被消去项的索引如何与递归调用处的索引匹配，并且在每个使用点上它们都是定义性的。此匹配会展开以处理一个到四个尾随的 [~=] 前提，可选地之前有三个隐式参数和一个同类的 [=] 前提，涵盖了本开发中实际出现的元数。
*)
Ltac reduce_jmeq :=
  repeat match goal with
  | [ H : ∀ _: _, _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl JMeq_refl)

  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl)
  end.

(*
 [reduce] runs [reduce_jmeq], then exhaustively breaks apart structured
 hypotheses left in the context: it collapses [existT] equalities via
 [inj_pair2] (relying on UIP for the index type) and destructs conjunctions,
 pairs, existentials, [sig] ([{x | P}]) and [sigT] ([{x & P}]) witnesses,
 substituting freed variables along the way.  The net effect is to flatten a
 tangle of dependent-equality and packaging hypotheses into their plain
 components. 

 --------
 [reduce] 运行 [reduce_jmeq]，然后彻底分解上下文中剩余的结构化假设：它通过 [inj_pair2]（依赖于索引类型的 UIP）折叠 [existT] 等式，并分解合取、对、存在量词、[sig]（[{x | P}]）和 [sigT]（[{x & P}]）证据，同时沿途替换释放的变量。总体效果是将依赖等式和封装假设的纠结结构展开为它们的基本组成部分。
*)
Ltac reduce :=
  reduce_jmeq;
  repeat (match goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          | [ H : { _ : _ | _ } |- _ ] => destruct H
          | [ H : { _ : _ & _ } |- _ ] => destruct H
          end; subst).

(*
 [inv H] is the usual "invert and clean up" idiom: derive the constructor
 constraints of [H] by [inversion], [subst] the resulting equations, discard
 the now-redundant [H], and finish with [reduce] to dispatch the dependent
 equalities (often [existT] equalities) that inversion of an indexed
 inductive leaves behind.  Used throughout to case-analyse the reduction and
 value judgements. 

 --------
 [inv H] 是常用的“反转并清理”惯用法：通过 [inversion] 得出 [H] 的构造函数约束，[subst] 得到的方程，丢弃现在多余的 [H]，并以 [reduce] 结束，以分发索引归纳反转留下的依赖等式（通常是 [existT] 等式）。在整个过程中用于对归约和值判断进行情况分析。
*)
Ltac inv H := inversion H; subst; clear H; reduce.

(*
 [equality] closes goals that are purely a matter of (dis)equality between
 constructor terms, combining propositional reasoning ([intuition]) with the
 congruence-closure decision procedure ([congruence]). 

 --------
 [equality]  解决纯粹涉及构造函数项之间（不）等式的目标，将命题推理（[intuition]）与同余闭包判定过程（[congruence]）结合起来。
*)
Ltac equality := intuition congruence.
