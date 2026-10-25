Require Import Coq.NArith.NArith.

Require Import Category.Lib.
Require Import Category.Lib.MapDecide.
Require Import Category.Theory.Metacategory.ArrowsOnly.

Generalizable All Variables.

Open Scope N_scope.

(** Worked examples for the arrows-only metacategory decision procedure / 仅箭头元范畴决策程序的示例解析 *)

(*
nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category

   These are not new results; they are a regression/demonstration suite tying
   together two pieces of machinery:

     - [Category.Theory.Metacategory.ArrowsOnly], which presents a category in
       Mac Lane's single-sorted ("arrows-only") form, with partial composition
       encoded as a finite map [pairs : M.t N] and a family of concrete finite
       metacategories built by [composable_pairs n] (the standard composable
       pairs of the n-object finite category, indexed via [triangular_number]);

     - [Category.Lib.MapDecide], a proof-by-reflection decision procedure for
       finite-map membership goals, exposed as the tactics [solve_map] and
       [map_decide] and the Gallina decider [formula_backward].

   The point of the examples is to exercise the decider on the very goals that
   arise when verifying that a [composable_pairs n] table really is a category:
   the associativity ("composition law") coherence between left- and
   right-associated composites. The interleaved timing comments contrast
   [map_decide] (reflective, fast) against the earlier brute-force tactic
   [destruct_maps; nomega], which blows up combinatorially as n grows. The
   examples are deliberately concrete and self-checking, so a regression in the
   decider surfaces as a build failure here rather than silently downstream.

--------
nLab：https://ncatlab.org/nlab/show/metacategory
nLab：https://ncatlab.org/nlab/show/category

这些不是新的结果；它们是一个回归/演示套件，将两套机制连接在一起：

- [Category.Theory.Metacategory.ArrowsOnly]，它以 Mac Lane 的单一分类（“仅箭头”）形式呈现，其中部分组合编码为有限映射 [pairs : M.t N]，以及由 [composable_pairs n] 构建的一族具体有限元范畴（n 对象有限范畴的标准可组合对，通过 [triangular_number] 索引）；

- [Category.Lib.MapDecide]，一种通过反射的有限映射成员目标证明决策过程，以战术 [solve_map] 和 [map_decide] 以及 Gallina 决策器 [formula_backward] 的形式公开。

这些例子的目的是让决策器针对在验证 [composable_pairs n] 表确实是一个范畴时出现的目标进行练习：即左结合和右结合复合之间的结合律（“复合法则”）一致性。交错的时间注释对比了 [map_decide]（反射型、快速）与较早的蛮力策略 [destruct_maps; nomega]，后者随着 n 的增加会组合爆炸。例子故意具体且自我检查，因此如果决策器回归问题，会在这里导致构建失败，而不是下游静默发生问题。
*)

(*
Sanity check on the raw decider [formula_backward] (the Gallina kernel
   behind [map_decide]), bypassing the reflection wrapper. The reified formula
   is the tautology [P -> P] for one fixed [P], and the goal asserts that the
   decider lands in its [Proved] branch ([then True]) rather than [No]/[Uncertain]
   ([else False]); [vm_compute] runs the decision and [constructor] closes the
   resulting [True]. The [vars] environment supplies the free positives 1..4;
   the answer does not depend on [x y z w], which only confirms the result is
   independent of the particular variable assignment.

--------
对原始判定器 [formula_backward]（[map_decide] 背后的 Gallina 内核）进行理智检查，绕过反射包装器。具象化的公式是对于固定的 [P] 的恒真式 [P -> P]，并且目标断言判定器会落入其 [Proved] 分支（[then True]），而不是 [No]/[Uncertain]（[else False]）；[vm_compute] 执行该判定，[constructor] 关闭由此产生的 [True]。[vars] 环境提供自由正数 1..4；答案不依赖于 [x y z w]，后者仅确认结果独立于特定的变量赋值。
*)
Example formula_backward_example (x y z w : N) :
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty)))
       {| vars := fun p =>
           if (p =? 1)%positive then x else
           if (p =? 2)%positive then y else
           if (p =? 3)%positive then z else
           if (p =? 4)%positive then w else 9%N |}
  then True else False.
Proof. vm_compute; constructor. Qed.

(*
Smallest end-to-end use of the reflective tactic [solve_map]: the same
   two-element map appears as hypothesis and conclusion, so [MapsTo (x,y) f]
   follows trivially. This checks the reify/decide/reflect round trip closes a
   genuine (non-vacuous) membership goal.

--------
反射策略 [solve_map] 的最小端到端使用：相同的两个元素的映射同时出现在假设和结论中，因此 [MapsTo (x,y) f] 自然地成立。这验证了 reify/decide/reflect 循环能够闭合一个真实的（非空）成员目标。
*)
Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

(*
The real content: the associativity coherence of [composable_pairs n].
   Following [ArrowsOnly]'s convention, [M.find (f, g) = Some fg] reads "g and
   f compose to fg" (i.e. [f ∘ g = fg]). So the hypotheses say [f ∘ g = fg],
   [g ∘ h = gh] and [fg ∘ h = fgh]; the conclusion says [f ∘ gh = fgh], i.e.
   the left- and right-associated composites of the triple agree. This is
   exactly the [composition_law] obligation discharged for [Three] in
   [ArrowsOnly], here stated directly against the composition table and closed
   by reflection. [vm_compute triangular_number] first normalises the index
   arithmetic so [map_decide] sees a ground map. The commented-out
   [destruct_maps; nomega] is the brute-force alternative, kept with its timing
   to document why reflection is used (0.016s vs 1.68s at n = 3).

--------
真实内容：[composable_pairs n] 的结合性一致性。遵循 [ArrowsOnly] 的约定，[M.find (f, g) = Some fg] 读作“g 和 f 组合为 fg”（即 [f ∘ g = fg]）。因此假设说 [f ∘ g = fg]、[g ∘ h = gh] 和 [fg ∘ h = fgh]；结论说 [f ∘ gh = fgh]，即三元组合的左结合和右结合一致。这正是 [composition_law] 在 [ArrowsOnly] 中为 [Three] 完成的义务，这里直接针对组合表陈述并通过反射闭合。[vm_compute triangular_number] 首先对索引算术进行规范化，因此 [map_decide] 可以看到一个底层映射。被注释掉的 [destruct_maps; nomega] 是蛮力替代方案，保留其时间记录以说明为何使用反射（n = 3 时 0.016 秒对比 1.68 秒）。
*)
Example problem3 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 3 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
(*
  destruct_maps; try nomega. (* takes 1.68s / destruct_maps；尝试 nomega。(* 花费 1.68 秒 *)
  Undo.
*)
  map_decide.                (* takes 0.016s / 耗时0.016秒 *)
Qed.

(*
Same associativity goal at larger n, showing how the two approaches scale.
   Brute force grows combinatorially with the table size (timings noted below:
   30.15s at n = 4, 2501s at n = 5), while reflection stays in the tens of
   milliseconds; the [destruct_maps] lines are commented out so the file builds
   quickly.

--------
在更大的 n 上相同的结合性目标，显示两种方法的扩展方式。暴力法随着表的大小呈组合增长（计时如下：n = 4 时为 30.15 秒，n = 5 时为 2501 秒），而反射法保持在几十毫秒；[destruct_maps] 行已被注释，以便文件快速构建。
*)
Example problem4 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 4 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 30.15s / destruct_maps；尝试 nomega。(* 花费 30.15 秒 *) *)
  (* Undo. / 撤销。 *)
  map_decide.                (* takes 0.035s / 耗时0.035秒 *)
Qed.

Example problem5 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 5 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 2501s / destruct_maps；尝试nomega。（*花费2501秒 *) *)
  (* Undo. / 撤销。 *)
  map_decide.                (* takes 0.085s / 耗时0.085秒 *)
Qed.

(*
Largest instance exercised here. Despite the name, this uses
   [composable_pairs 10] (a 10-object table, the 100 alludes to the roughly
   hundred-entry map), and is the only case where reflection itself takes
   appreciable time (2.445s); brute force is not even attempted.

--------
这里演示的最大实例。尽管名称如此，这里使用的是 [composable_pairs 10]（一个包含 10 个对象的表，100 指的大约有一百个条目的映射），并且这是唯一一个反射本身需要显著时间（2.445秒）的情况；暴力破解甚至都没有尝试。
*)
Example problem100 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 10 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. / 销毁地图；试试 nomega。 *)
  (* Undo. / 撤销。 *)
  map_decide.                (* takes 2.445s / 耗时 2.445 秒 *)
Qed.
