# 12 · 在 Sets / Cat / Coq 上落地

把前面定义接到具体范畴；验证「CTFP 例子」在本库有宿主。

## 范畴论陈述

- **Sets**：setoid 与尊重 `≈` 的映射（Bishop 风格），支撑 Yoneda/伴随里出现的 `Sets`。
- **Cat**：对象为范畴、态射为函子（至多自然同构意义下的等式依文件约定）。
- **Coq / Theory.Coq**：把 Gallina 类型与函数接到一般理论（见根 README「编程子库」）。

## 编程直觉

CTFP 的 Hask ≈ 理想化 Haskell；本库用 `Sets` + `Theory/Coq` 分担「集合」与「程序」两角。

## 路径与 Require

```coq
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Coq.
Require Import Category.Instance.FinSet.     (* Lawvere 等 *)
Require Import Category.Instance.Mon.        (* 幺半例子，按需 *)
```

其它常用：`Discrete`、`One`、`Two`、`Top`、`Vect`、`Adj`……见 `Instance/` 目录名。

## 关键摘录

```coq
(* Instance/Sets.v *)
Record SetoidObject := {
  carrier :> Type;
  is_setoid :> Setoid carrier
}.
Record SetoidMorphism `{Setoid x} `{Setoid y} := {
  morphism :> x → y;
  proper_morphism :> Proper (respectful equiv equiv) morphism
}.
```

`Cat`：`Instance Cat : Category := {| ... |}`（态射为函子）。

## CoqIDE 步骤

1. `Instance/Sets.v`：解释到 `Sets` 范畴实例；看 mono/iso 引理（`injectivity_is_monic` 等）。
2. `Instance/Cat.v`：对象/态射字段；与 `Theory/Functor.v` 对照。
3. 挑一个前面概念（积 / Monad）在 `Sets` 或 `Coq` 中搜 `Instance`，完成「定义 → 例子」闭环。
4. Lawvere 用户：回到 [11](11-lawvere-free.md) 的 `FinSet` 路径实际 Compile Buffer。

## 和入门教程的关系

环境、扩展约定仍看 [../01-setup.md](../01-setup.md)、[../06-extending.md](../06-extending.md)。本系列到此收束主线；Applicative / Comonad / Optics 可按 INDEX 缺口加篇。
