Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** A CEK abstract machine for the de Bruijn STLC / 用于 de Bruijn STLC 的 CEK 抽象机 *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/CEK_Machine

 This file gives an environment-machine evaluator for the de Bruijn STLC of
 Exp.v, in the style of the CEK machine of Felleisen and Friedman: a
 left-to-right call-by-value abstract machine whose state triples a Control
 term, an Environment, and a Kontinuation.  Here a machine state is a [Σ]
 pairing a closed control [Closure] (a term together with the environment
 that closes its free variables) with an [EvalContext] continuation:

 Σ τ          := MkΣ (c : Closed u) (κ : EvalContext u τ)
 Closed τ     := Closure (e : Exp Γ τ) (ρ : ClEnv Γ)   (control + env)
 ClEnv Γ      := a list of [Value]s, one per type in Γ   (the environment)
 EvalContext  := the reified continuation / evaluation context

 [step] is the one-step transition function on states; [loop gas] iterates it
 a fixed number of times (the [gas]/fuel makes evaluation total, since the
 STLC is strongly normalizing but [step] is not structurally recursive);
 [inject] loads a closed term into the initial state [MkΣ (Closure e NoCl) MT]
 with the empty environment and halt continuation [MT]; and [run gas e] is the
 composite [loop gas (inject e)].

 FLAG (meta-theory / correctness): pair evaluation is presently broken, so
 this machine does NOT agree with the call-by-value operational semantics of
 Step.v on terms involving products.  Two related defects:

 - The PAIR_FST/PAIR_SND continuations do not gate on whether a component
 is already a value.  Starting from [Closure (Pair x y) ρ] under any
 continuation κ, the clauses at the [Pair]/[PAIR_SND]/[PAIR_FST] cases
 form a 3-cycle that stashes both components away unevaluated and then
 rebuilds the *original* pair, so neither x nor y is ever reduced.  For
 example, [run 100 (Pair (APP (LAM (VAR ZV)) EUnit) EUnit)] cycles back
 to the syntactic input rather than reducing the redex in the first
 component (this is also why [example_pair] in Example.v holds only
 because its gas count lands on a multiple of the cycle length).

 - The [FN] continuation (a function value awaiting its evaluated argument)
 only dispatches when the argument's control is [EUnit] or [LAM]; there
 is no clause for a [Pair] argument.  A pair argument therefore falls
 into the [Pair] 3-cycle above and the application never fires, e.g.
 [run gas (APP (LAM (VAR ZV)) (Pair EUnit EUnit))] never terminates in a
 value for any [gas].

 The intended correctness statement (an agreement theorem relating [run] to
 [--->*] of Step.v / Multi.v, or to [SemExp] of Sem.v) is sketched but
 unproven at the end of this file.  Fixing the pair cases (have PAIR_SND only
 swap once its component is a value, and add a [FN] clause that applies the
 saved function to a [Pair]-valued argument) is left as future work; it
 touches the [step] equation graph and the [eq_refl] computations in
 Example.v, so it is deliberately not attempted as part of this review.

 References:
 CEK / environment machine
 https://en.wikipedia.org/wiki/CEK_Machine
 small-step CBV operational semantics (the relation this should agree with)
 Instance/Lambda/Step.v, Instance/Lambda/Multi.v 

 --------
 维基百科:  https://en.wikipedia.org/wiki/CEK_Machine

 本文件为 Exp.v 的 de Bruijn STLC 提供了一个环境-机器评估器，采用 Felleisen 和 Friedman 的 CEK 机器风格：一种从左到右的按值调用抽象机器，其状态将控制项、环境和延续组合成三元组。这里机器状态是一个 [Σ] 配对，包含一个闭合控制项 [Closure]（一个项及其闭合自由变量的环境）和一个 [EvalContext] 延续：

 Σ τ          := MkΣ (c : Closed u) (κ : EvalContext u τ)
 Closed τ     := Closure (e : Exp Γ τ) (ρ : ClEnv Γ)   （控制 + 环境）
 ClEnv Γ      := 每种类型在 Γ 中对应一个 [Value] 的列表   （环境）
 EvalContext  := 具象化的延续/评估上下文[step] 是状态上的一步转换函数；[loop gas] 对其进行固定次数的迭代（[gas] /燃料使评估完整，因为 STLC 是强归约的，但 [step] 并非结构递归）；[inject] 将封闭项加载到初始状态 [MkΣ (Closure e NoCl) MT] 中，带有空环境和停止续体 [MT]；[run gas e] 是复合的 [loop gas (inject e)]。

 标记（元理论 / 正确性）：对偶评估目前存在问题，因此此机器在涉及积的项上不符合 Step.v 的按值调用操作语义。有两个相关缺陷：- PAIR_FST/PAIR_SND 的延续不会基于某个组件是否已经是值而进行控制。从 [Closure (Pair x y) ρ] 开始，在任何延续 κ 下，[Pair] / [PAIR_SND] / [PAIR_FST] 分支的条款形成一个三循环，它会将两个组件都存放起来而不求值，然后重建*原始*的 pair，因此 x 和 y 都不会被化简。例如，[run 100 (Pair (APP (LAM (VAR ZV)) EUnit) EUnit)] 会循环回到语法输入，而不是化简第一个组件中的简约项（这也是为什么 Example.v 中的 [example_pair] 成立，仅仅是因为它的 gas 计数落在循环长度的倍数上）。- [FN] 的延续（一个等待其计算参数的函数值）  
 只有在参数的控制为 [EUnit] 或 [LAM] 时才会调度；对于 [Pair] 参数没有对应的分支。因此一个成对参数会落入上面的 [Pair] 3-循环中，应用程序永远不会触发，例如，对于任何 [gas]，[run gas (APP (LAM (VAR ZV)) (Pair EUnit EUnit))] 永远不会终止为一个值。预期的正确性声明（一个关于 Step.v / Multi.v 的 [run] 与 [--->*]，或关于 Sem.v 的 [SemExp] 的一致性定理）在本文件末尾有概述，但未证明。修复成对情况（仅在组件为值时才让 PAIR_SND 交换一次，并添加一个将保存的函数应用于 [Pair] 值参数的 [FN] 条款）作为未来工作；它涉及 Example.v 中的 [step] 方程图和 [eq_refl] 计算，因此审查过程中故意未尝试。 参考文献： CEK / 环境机 https://en.wikipedia.org/wiki/CEK_Machine 小步 CBV 操作语义（此应与其一致的关系） Instance/Lambda/Step.v、Instance/Lambda/Multi.v
*)

Set Transparent Obligations.

Section Eval.

Import ListNotations.

(*
 A [Closed] is the machine's control: an [Exp] paired with a [ClEnv] that
 closes its free de Bruijn variables.  A [ClEnv Γ] is the environment, one
 [Value] per type in Γ.  A [Value] is a closure whose body is already a value
 ([ValueP] witnesses that it does not reduce). 

 --------
 [Closed] 是机器的控制：一个 [Exp] 与一个 [ClEnv] 配对，用于闭合它的自由 de Bruijn 变量。[ClEnv Γ] 是环境，Γ 中每种类型一个 [Value]。[Value] 是一个闭包，其主体已经是一个值（[ValueP] 证明它不会再归约）。
*)
Inductive Closed : Ty → Set :=
  | Closure {Γ τ} : Exp Γ τ → ClEnv Γ → Closed τ

with ClEnv : Env → Set :=
  | NoCl : ClEnv []
  | AddCl {Γ τ} : Value τ → ClEnv Γ → ClEnv (τ :: Γ)

with Value : Ty → Set :=
  | Val {Γ τ} (x : Exp Γ τ) : ValueP x → ClEnv Γ → Value τ.

Derive Signature NoConfusion NoConfusionHom Subterm for ClEnv Closed Value.

(* Environment lookup: project the [Value] bound to variable [v]. Total by intrinsic typing -- [NoCl] has no variables, so the empty-env cases are absurd and elided by Equations. / 环境查找：将 [Value] 投影到绑定到变量 [v] 上。通过内在类型总计——[NoCl] 没有变量，因此空环境情况是荒谬的，并且被方程省略。 *)
Equations get_val `(s : ClEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_val (AddCl x _)  ZV     := x;
  get_val (AddCl _ xs) (SV v) := get_val xs v.

(* Concatenate two environments, mirroring [++] on the underlying contexts. / 连接两个环境，在底层上下文上镜像 [++]。 *)
Equations combine `(c1 : ClEnv Γ) `(c2 : ClEnv Γ') : ClEnv (Γ ++ Γ') :=
  combine NoCl         c2 := c2;
  combine (AddCl c c1) c2 := AddCl c (combine c1 c2).

(*
 Append [x] to the end of [xs].  NOTE: unused anywhere in the development,
 and the cons case shadows the parameter [x] with the list head, so this
 actually duplicates the last element instead of appending the argument
 ([snoc a [b;c]] computes [[b;c;c]], not [[b;c;a]]).  Kept and corrected
 here for clarity since it is dead code. 

 --------
 将 [x] 附加到 [xs] 的末尾。注意：在开发中未被使用，并且构造函数中的情况用列表头覆盖了参数 [x]，因此这实际上是复制最后一个元素而不是追加参数（[snoc a [b;c] 计算 [[b;c;c]，而不是 [[b;c;a]）。为清晰起见，在这里保留并修正，因为这是死代码。
*)
Fixpoint snoc {a : Type} (x : a) (xs : list a) : list a :=
  match xs with
  | [] => [x]
  | y :: ys => y :: snoc x ys
  end.

(*
 The reified continuation / evaluation context.  [EvalContext u τ] is a stack
 of pending eliminations turning a value of type [u] into a final result of
 type [τ]: [MT] is the empty context (halt); [AR]/[FN] sequence a function
 then its argument for application; the PAIR/FST/SND frames sequence the
 evaluation of products and their projections. 

 --------
 具体化的继续/求值上下文。[EvalContext u τ] 是一个待处理消解的栈，将类型为 [u] 的值转化为类型为 [τ] 的最终结果：[MT] 是空上下文（停止）；[AR] / [FN] 按顺序执行函数及其参数应用；PAIR/FST/SND 帧按顺序评估积及其投影。
*)
Inductive EvalContext : Ty → Ty → Set :=
  | MT {τ} : EvalContext τ τ
  | AR {dom cod τ} :
    Closed dom → EvalContext cod τ → EvalContext (dom ⟶ cod) τ
  | FN {dom cod τ} :
    Value (dom ⟶ cod) → EvalContext cod τ → EvalContext dom τ
  | PAIR_FST {τ1 τ2 τ} : Closed τ1 → EvalContext (τ1 × τ2) τ → EvalContext τ2 τ
  | PAIR_SND {τ1 τ2 τ} : Closed τ2 → EvalContext (τ1 × τ2) τ → EvalContext τ1 τ
  | FST {τ1 τ2 τ} : EvalContext τ1 τ → EvalContext (τ1 × τ2) τ
  | SND {τ1 τ2 τ} : EvalContext τ2 τ → EvalContext (τ1 × τ2) τ.

Derive Signature NoConfusion NoConfusionHom Subterm for EvalContext.

(*
 A machine state: a control [Closed] of type [u] together with a continuation
 that will turn a [u]-result into the final [τ]-result. 

 --------
 机器状态：一种类型为 [u] 的控制 [Closed]，以及一个将 [u] 结果转变为最终 [τ] 结果的延续。
*)
Inductive Σ : Ty → Set :=
  | MkΣ {u    : Ty}
        (exp  : Closed u)
        {τ    : Ty}
        (knt  : EvalContext u τ) : Σ τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Σ.

(*
 The one-step transition relation of the machine, as a total function on
 states.  A non-[MT] continuation drives evaluation forward; reaching [MT]
 with a value is the only fixed point ([step (MkΣ c MT) := MkΣ c MT]).  See
 the file header for the FLAG on the product cases, which fail to reduce pair
 components and so diverge from the operational semantics of Step.v. 

 --------
 机器的一步迁移关系，作为状态上的一个全函数。一个非 [MT] 的延续推动计算向前；达到带有值的 [MT] 是唯一的固定点（[step (MkΣ c MT) := MkΣ c MT]）。有关产品情况的 FLAG，请参见文件头，这些情况无法化简对组件，因此偏离 Step.v 的操作语义。
*)
Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* Constants / 常量 *)
  step (MkΣ (Closure EUnit _) (FN f κ)) with f := {
    | Val (LAM e) _ ρ' := MkΣ (Closure e (AddCl (Val EUnit UnitP NoCl) ρ')) κ;
  };

  step (MkΣ (Closure (Fst p) ρ) κ) := MkΣ (Closure p ρ) (FST κ);
  step (MkΣ (Closure (Snd p) ρ) κ) := MkΣ (Closure p ρ) (SND κ);

  step (MkΣ (Closure (Pair x y) ρ) (FST κ)) := MkΣ (Closure x ρ) κ;
  step (MkΣ (Closure (Pair x y) ρ) (SND κ)) := MkΣ (Closure y ρ) κ;

  (*
 FLAG: these three product clauses never reduce a pair's components.  The
 [PAIR_SND] swap below fires regardless of whether the control is a value,
 so it stashes both components away unevaluated; [PAIR_FST] then rebuilds
 the original pair, closing a 3-cycle.  A correct version would gate the
 [PAIR_SND] swap on [ValueP] of the first component (so the first component
 is evaluated before moving to the second).  See the file header. 

 --------
 标记：这三个产品子句从不减少一对的组成部分。下面的 [PAIR_SND]  交换会触发，无论控制是否为一个值，因此它会将两个组件都未求值地存放起来；然后 [PAIR_FST]  重建原始的对，形成一个三循环。一个正确的版本会在第一个组件的 [ValueP] 上控制 [PAIR_SND]  交换（因此第一个组件在移动到第二个组件之前会被求值）。请参阅文件头。
*)
  step (MkΣ (Closure (Pair x y) ρ) κ) :=
    MkΣ (Closure x ρ) (PAIR_SND (Closure y ρ) κ);
  step (MkΣ x (PAIR_SND y κ)) := MkΣ y (PAIR_FST x κ);
  step (MkΣ (Closure y ρ) (PAIR_FST (Closure x ρ') κ)) :=
    MkΣ (Closure (Pair (liftL _ x) (liftR _ y)) (combine ρ' ρ)) κ;

  (*
 A variable might lookup a lambda, in which case continue evaluating down
 that vein; otherwise, if no continuation, this is as far as we can go. 

 --------
 一个变量可能会查找一个 lambda，在这种情况下，继续沿着该方向进行求值；否则，如果没有后续，这就是我们能进行的最远的步骤。
*)
  step (MkΣ (Closure (VAR v) ρ) κ) with get_val ρ v := {
    | Val val _ ρ' := MkΣ (Closure val ρ') κ
  };

  (* If a lambda is passed, call it with the continuation / 如果传入了一个 lambda，则用 continuation 调用它 *)
  step (MkΣ (Closure (LAM e) ρ) (AR a κ)) :=
    MkΣ a (FN (Val (LAM e) (LambdaP _) ρ) κ);
  step (MkΣ (Closure (LAM e) ρ) (FN (Val (LAM f) _ ρ') κ)) :=
    MkΣ (Closure f (AddCl (Val (LAM e) (LambdaP _) ρ) ρ')) κ;

  (* Application evaluates the lambda and then the argument / 应用先评估 lambda，然后评估参数 *)
  step (MkΣ (Closure (APP f x) ρ) κ) :=
    MkΣ (Closure f ρ) (AR (Closure x ρ) κ);

  step (MkΣ c MT) := MkΣ c MT.

(*
 Iterate [step] a bounded number of times.  The [gas] (fuel) parameter makes
 evaluation total: [step] is not structurally recursive, so [loop] recurs on
 the gas rather than on the state.  With enough gas a normalizing run reaches
 an [MT] fixed point and stays there. 

 --------
 对  [step]  迭代有限次。  [gas]（燃料）参数使得评估总数：[step] 不是结构递归的，所以 [loop] 递归在燃料上而不是状态上。  在足够的燃料下，归一化运行达到 [MT] 不动点并停留在那里。
*)
Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s := loop gas' (step s).

(*
 Load a closed term into the initial machine state: the empty environment
 [NoCl] closes its (nonexistent) free variables, and the halt continuation
 [MT] will receive the final value. 

 --------
 将一个封闭项加载到初始机器状态：空环境
 [NoCl]  封闭它的（不存在的）自由变量，停止延续
 [MT]  将接收最终值。
*)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ (Closure e NoCl) MT.

(* Evaluate a closed term for [gas] steps from its initial state. / 从其初始状态评估闭合项 [gas] 的步骤。 *)
Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

(*
 Intended agreement theorem (unproven; see the FLAG in the file header).
 The machine should agree with the call-by-value operational semantics of
 Step.v / Multi.v, roughly:

 forall (e v : Exp [] τ), ValueP v ->
 (e --->* v  <->  exists gas, run gas e = inject v)

 i.e. [run] reaches the injected normal form exactly when [e] reduces to it.
 Equivalently it should agree with the denotational semantics [SemExp] of
 Sem.v.  No such lemma is established here: an earlier draft contained a
 placeholder script that referenced a nonexistent lemma [all_exprs_complete]
 and did not typecheck, so it has been replaced by this note.  Note that any
 such theorem is currently false on terms with products because of the pair
 defect documented above; correcting [step]'s product cases is a prerequisite
 for stating and proving agreement. 

 --------
 预期一致性定理（未证明；参见文件头的 FLAG）。
 该机器应与 Step.v / Multi.v 的按值调用操作语义一致，大致如下：

 对于所有 (e v : Exp [] τ)，如果 ValueP v 成立，则有：
 (e --->* v  <->  存在 gas，使得 run gas e = inject v)也就是说，当 [e] 归约到它时，[run] 恰好达到注入的正规形。等价地，它应该与 Sem.v 的指称语义 [SemExp] 一致。这里没有建立这样的引理：早期的草稿包含一个占位脚本，引用了一个不存在的引理 [all_exprs_complete]，并且无法通过类型检查，因此已被此说明替代。请注意，由于上文记录的对偶缺陷，任何此类定理在包含乘积的项上当前都是错误的；在陈述和证明一致性之前，修正 [step] 的乘积情况是前提条件。
*)

End Eval.
