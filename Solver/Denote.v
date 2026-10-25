From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

(**
* Denotation: interpreting reified terms back into a category

    This file is the semantic anchor of the reflective solver: the decision
    procedure works by reflection, computing on a syntactic mirror of the goal
    rather than reasoning about it directly
    (https://en.wikipedia.org/wiki/Computational_reflection).  Reification
    (Solver/Reify.v) turns a goal about concrete morphisms into a syntactic
    [Term]/[Expr]; here we interpret that syntax back into the morphisms it
    came from, using the environment carried by [Arrows].  Soundness of the
    decision procedure means: every rewrite Normal.v performs on the syntax
    must be invisible under this denotation.

    The [Term] grammar is the free category on the reified arrows
    (https://ncatlab.org/nlab/show/free+category): objects are [nat] indices
    into [objs] (via [objD]), [Ident] denotes the identity, [Comp] denotes
    composition, and [Morph a] denotes the [a]th reified generator.  A [Term]
    is intrinsically untyped (it does not record its own domain/codomain), so
    [termD_work] is given a domain and *computes* the codomain by threading
    types through the composition, returning the result as a dependent pair
    [∃ cod, objD dom ~> objD cod]; partiality ([option]) absorbs ill-typed
    syntax such as a [Comp] whose middle objects disagree or a [Morph]
    referring to a generator of the wrong domain.

--------
* 指称：将具体化的术语重新解释为一个类别

该文件是反射求解器的语义锚点：决策程序通过反射工作，在目标的语法镜像上进行计算，而不是直接对其进行推理（https://en.wikipedia.org/wiki/Computational_reflection).  具体化（Solver/Reify.v）将关于具体态射的目标转化为语法形式[Term]/[Expr]；在这里，我们使用 [Arrows] 携带的环境，将该语法重新解释回它所来源的态射。决策程序的可靠性意味着：Normal.v 对语法执行的每一次重写在此表示下都必须是不可见的。）

[Term] 语法是在具象化箭头上的自由范畴（https://ncatlab.org/nlab/show/free+category): 对象是 [nat] 在 [objs] 中的索引（通过 [objD]），[Ident] 表示恒等，[Comp] 表示组合，[Morph a] 表示第 [a] 个具象化生成元。一个 [Term] 本质上是无类型的（它不记录自身的定义域/值域），所以 [termD_work] 被赋予一个定义域并通过在组合中传递类型来*计算*值域，将结果作为依赖对 [∃ cod, objD dom ~> objD cod] 返回；部分性（[option]）会吸收类型错误的语法，例如中间对象不一致的 [Comp] 或引用了错误定义域生成元的 [Morph]。
*)

Section Denote.

Context `{Arrows}.

Open Scope nat_scope.

(**
Look up the [f]th reified generator, requiring its domain to be [dom].
    The stored type [tys[f] = (d', c')] supplies the codomain [cod := c']; we
    then ask [ith_exact] (Lib/IList.v) for the arrow at position [f] indexed by
    [(dom, cod)], which succeeds only when [dom] matches the stored domain
    [d'].  On success we return the arrow paired with its computed codomain;
    an out-of-range [f] or a domain mismatch yields [None].  The default
    index [(0, 0)] handed to [List.nth] is never observed on the success
    path, since a missing [tys] entry forces [ith_exact] to fail.

--------
查找 [f] 重构生成器，需要其域为 [dom]。存储的类型 [tys[f] = (d', c')] 提供余域 [cod := c']；然后我们请求 [ith_exact] (Lib/IList.v) 获取由 [(dom, cod)] 索引的位于位置 [f] 的箭头，当且仅当 [dom] 与存储的域 [d'] 匹配时才会成功。成功时，我们返回与其计算余域配对的箭头；超出范围的 [f] 或域不匹配会产生 [None]。传递给 [List.nth] 的默认索引 [(0, 0)] 在成功路径上从未被观察到，因为缺失的 [tys] 条目会导致 [ith_exact] 失败。
*)
Definition lookup_arr (f : nat) dom :
  option (∃ cod, objD dom ~> objD cod) :=
  let cod := snd (List.nth f tys (0, 0)) in
  match ith_exact f (dom, cod) arrs with
  | Some f => Some (cod; f)
  | _ => None
  end.

(**
Denote a [Term] starting from domain [dom], computing its codomain.
    [Ident] is the identity [id : objD dom ~> objD dom].  For [Comp f g] we
    interpret the *right* argument [g] first (from [dom] to some middle object
    [mid]), then [f] from [mid] onward; the result [f ∘ g] composes them in
    diagrammatic-domain order, so [Comp f g] denotes [f ∘ g] exactly as
    reification produced it from [f ∘ g].  The middle object [mid] computed
    for [g] is fed as the domain of [f], which is what makes [f ∘ g] well
    typed; if either subterm fails to denote the whole [Comp] fails.

--------
表示一个从域 [dom] 开始的 [Term]，并计算它的余域。[Ident] 是恒等的 [id : objD dom ~> objD dom]。对于 [Comp f g]，我们首先解释 *右* 参数 [g]（从 [dom] 到某个中间对象 [mid]），然后解释 [f] 从 [mid] 开始；结果 [f ∘ g] 按照图示域顺序组合它们，因此 [Comp f g] 精确表示了 [f ∘ g]，就像具象化从 [f ∘ g] 得到它一样。为 [g] 计算的中间对象 [mid] 被用作 [f] 的域，这就是使 [f ∘ g] 类型正确的原因；如果任一子项未能表示整体，则 [Comp] 也会失败。
*)
Fixpoint termD_work dom (e : Term) :
  option (∃ cod, objD dom ~> objD cod) :=
  match e with
  | Ident => Some (dom; id)
  | Morph a => lookup_arr a dom
  | Comp f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Import EqNotations.

(**
Denote a [Term] at a *fixed* codomain [cod].  [termD_work] computes
    whatever codomain [y] the term actually has; we then check [y = cod] with
    decidable equality on [Obj] and, on a match, rewrite the morphism along
    that proof to land in [objD dom ~> objD cod].  A codomain mismatch yields
    [None].  The rewrite uses only the [eq_dec] evidence, so this remains
    axiom-free.

--------
在一个*固定*的余域 [cod] 上表示一个 [Term]。[termD_work] 计算项实际具有的余域 [y]；然后我们使用 [Obj] 上的可判定等式检查 [y = cod]，并在匹配时沿该证明重写态射以落在 [objD dom ~> objD cod] 中。余域不匹配会导致 [None]。该重写仅使用 [eq_dec] 的证据，因此仍然是无公理的。
*)
Definition termD dom cod (e : Term) :
  option (objD dom ~> objD cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left H => Some (rew [fun y => _ ~> objD y] H in f)
    | _ => None
    end
  | _ => None
  end.

(**
Denote an [Expr] (a propositional combination of morphism equations) as
    a [Type], reading the logical connectives into their [Type]-level
    counterparts: [Top]/[Bottom] as [True]/[False], [And]/[Or]/[Impl] as
    [∧]/[+]/[→].  A leaf [Equiv d c f g] denotes the proposition that the two
    terms, interpreted at domain [d] and codomain [c], are equal morphisms
    ([f ≈ g], the homset setoid equivalence); if either term fails to denote
    at those types the equation is read as [False].  This is the goal that
    Reify.v changes the original conjecture into, and whose truth Decide.v
    establishes by reflection.

--------
将 [Expr]（一个形态方程的命题组合）表示为 [Type]，将逻辑连接词读取为它们的 [Type] 级对应项：[Top]/[Bottom] 作为 [True]/[False]，[And]/[Or]/[Impl] 作为 [∧]/[+]/[→]。一个叶子 [Equiv d c f g] 表示命题，即在域 [d] 和陪域 [c] 下解释的两个项是相等的态射（[f ≈ g]，同态集的集合等价）；如果任何一个项在这些类型上无法表示，该方程被读作 [False]。这是 Reify.v 将原始猜想转化为的目标，并且 Decide.v 通过反射来建立其真值。
*)
Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top      => True
  | Bottom   => False
  | And p q  => exprD p ∧ exprD q
  | Or p q   => exprD p + exprD q
  | Impl p q => exprD p → exprD q

  | Equiv d c f g =>
    match termD d c f, termD d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  end.

End Denote.
