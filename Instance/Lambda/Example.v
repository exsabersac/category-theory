Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Eval.

Set Equations With UIP.

Generalizable All Variables.

(* * * Worked examples for the de Bruijn STLC CEK evaluator / * * de Bruijn STLC CEK 求值器的示例解析 *)

(*
 These [Definition]s exercise the CEK machine of Eval.v on concrete closed
 terms, pinning each [run gas e] to the exact final machine state it computes.
 The proofs are [eq_refl], so each one is a regression test: it typechecks
 precisely when the machine still reduces the term to the stated state, by
 the definitional unfolding of [run]/[loop]/[step].

 CEK machine:  https://en.wikipedia.org/wiki/CEK_Machine
 simply typed lambda calculus:
 https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus 

 --------
 这些 [Definition] 练习在具体封闭项上对 Eval.v 的 CEK 机进行操作，将每个 [run gas e] 精确地固定到它计算出的最终机器状态。证明是 [eq_refl] ，因此每一个都是回归测试：仅当机器通过 [run] / [loop] / [step] 的定义展开仍将该项化简到所述状态时，它才会类型检查通过。

 CEK 机：https://en.wikipedia.org/wiki/CEK_Machine
 简单类型 lambda 演算：
 https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
*)

Section Example.

Open Scope Ty_scope.

(*
 A pure function example, with no products: [((λx. x (λ_. ())) (λy. y)) ()].
 Reducing call-by-value, [(λx. x (λ_. ())) (λy. y)] applies [λy. y] to
 [λ_. ()], giving [λ_. ()]; applying that to [()] yields [()].  The machine
 halts at [Closure EUnit] -- the body of the final [λ_. ()] -- under the
 two-entry environment that bound its argument [()] and the earlier [λy. y],
 with the halt continuation [MT]. 

 --------
 一个纯函数示例，没有产品：[((λx. x (λ_. ())) (λy. y)) ()]。
 通过按值调用进行简化，[(λx. x (λ_. ())) (λy. y)] 将 [λy. y] 应用于 [λ_. ()]，得到 [λ_. ()]；将其应用于 [()] 得到 [()]。机器在 [Closure EUnit] 停止——最终 [λ_. ()] 的主体——在绑定其参数 [()] 和先前的 [λy. y] 的双入口环境下，停止续延为 [MT]。
*)
Definition example1 :
  run 20 (APP (APP (LAM (APP (VAR ZV)
                             (LAM EUnit)))
                   (LAM (VAR ZV)))
              EUnit) =
    MkΣ (Closure EUnit
                 (AddCl (Val EUnit Value.UnitP NoCl)
                        (AddCl (Val (LAM (cod:=_) (VAR ZV))
                                    (Value.LambdaP (VAR ZV)) NoCl) NoCl))) MT :=
  eq_refl.

(*
 CAUTION: this example documents the product defect FLAGged in Eval.v, NOT a
 correct evaluation.  The two components [(λx. x) ()] are redexes that SHOULD
 each reduce to [()], so a correct CBV machine would return [Pair () ()].
 Instead the [Pair]/[PAIR_SND]/[PAIR_FST] clauses of [step] form a 3-cycle
 that stashes the components away unevaluated and rebuilds the original pair;
 the result below is the *syntactically unchanged* input term.  The equation
 holds at gas 30 only because 30 is a multiple of the cycle length, landing
 the machine back at its start.  See the file header of Eval.v. 

 --------
 注意：此示例记录了在 Eval.v 中标记的产品缺陷，而不是正确的评估。两个组件 [(λx. x) ()] 是应当化简的 redex，每个都应化简为 [()]，因此一个正确的 CBV 机器应该返回 [Pair () ()]。相反，[step] 的 [Pair] / [PAIR_SND] / [PAIR_FST] 子句形成了一个 3 循环，将组件存放起来而不进行评估，并重建原始对；下面的结果是*语法上未改变*的输入项。该等式在 gas 30 时成立只是因为 30 是循环长度的倍数，使机器回到起点。详见 Eval.v 的文件头。
*)
Definition example_pair :
  run 30 (Pair (APP (LAM (VAR ZV)) EUnit)
               (APP (LAM (VAR ZV)) EUnit)) =
    MkΣ (Closure
           (Pair (APP (LAM (VAR ZV)) EUnit) (APP (LAM (VAR ZV)) EUnit)) NoCl) MT :=
  eq_refl.

(*
 Projection avoids the [Pair] 3-cycle above: [step] on [Fst]/[Snd] pushes an
 [FST]/[SND] frame, and the [Pair]-against-[FST]/[SND] clauses grab the chosen
 component directly ([Fst (Pair x y)] selects [x]) and then evaluate it.  Here
 the selected component [(λx. x) ()] reduces to [()], so both projections halt
 at [Closure EUnit], the correct call-by-value result. 

 --------
 投影避免了上面的 [Pair] 3-循环：[step] 在 [Fst] / [Snd] 上推动一个 [FST] / [SND] 框架，而 [Pair] 对抗 [FST] / [SND] 条款直接抓取所选组件（[Fst (Pair x y)] 选择 [x]），然后进行求值。在这里，所选组件 [(λx. x) ()] 归约为 [()]，因此两个投影在 [Closure EUnit] 停止，这是正确的按值调用结果。
*)
Definition example_fst :
  run 20 (Fst (Pair (APP (LAM (VAR ZV)) EUnit)
                    (APP (LAM (VAR ZV)) EUnit))) =
    MkΣ (Closure EUnit NoCl) MT := eq_refl.

Definition example_snd :
  run 20 (Snd (Pair (APP (LAM (VAR ZV)) EUnit)
                    (APP (LAM (VAR ZV)) EUnit))) =
    MkΣ (Closure EUnit NoCl) MT := eq_refl.

End Example.
