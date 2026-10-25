(**
* The reflective categorical-equality solver (umbrella import).

   Re-exports the proof-by-reflection decision procedure for equalities of
   morphisms in a free category: [Reify] (Ltac that reflects a goal into
   abstract syntax), [Normal] (the free-category normal form and its
   denotation-preserving soundness), and [Decide] (the decision procedure
   and its soundness theorem).  Import this to get the [categorical] /
   [normalize] tactics.

--------
* 反射范畴等式求解器（总导入）。

重新导出自由范畴中态射等式的反射证明决策过程：[Reify]（将目标反射为抽象语法的Ltac）、[Normal]（自由范畴的规范形式及其保真性定理）、以及[Decide]（决策过程及其可靠性定理）。导入此模块以获取 [categorical] / [normalize] 策略。
*)

Require Export Category.Solver.Reify.
Require Export Category.Solver.Normal.
Require Export Category.Solver.Decide.
