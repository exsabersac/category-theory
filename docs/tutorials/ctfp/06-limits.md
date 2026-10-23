# 06 · 极限与相关构造

**CTFP**：Part Two Ch.2 *Limits and Colimits*。

## 范畴论陈述

极限 = 锥的泛性质：对图 `F : J ⟶ C`，极限对象配投影锥，任意锥唯一分解。特例：终对象（空图）、积、equalizer、pullback。余极限对偶。

## 编程直觉

「最经济的共享结构」：pullback ≈ 数据库自然 join；equalizer ≈ 两函数的解集。

## 路径与 Require

```coq
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Pullback.
(* Kan 观点下的极限： *)
(* Structure/Limit/Kan 等子路径，按目录浏览 *)
```

| 路径 | 作用 |
|------|------|
| `Structure/Cone.v`、`Cone/` | 锥 |
| `Structure/Limit.v`、`Limit/` | 极限 |
| `Structure/Equalizer*` | 均衡子 |
| `Structure/Pullback*` | 拉回 |
| `Structure/Complete*` | 完备性 |
| `Structure/Limit/Kan` 等 | 与 Kan 扩张的联系 |

## 关键摘录

先读 `Structure/Limit.v` / `Cone.v` 文首导言，再定位主 `Class`（名称可能是 `Limit` / `IsLimit` 等）。阅读线索：

1. 图 = 函子 `J ⟶ C`；
2. 锥 = 从顶点到图的自然族；
3. 极限 = 泛锥（UMP）。

Equalizer / Pullback 文件通常直接给出特例 UMP，可比主定义更易上手。

## CoqIDE 步骤

1. `Structure/Cone.v` → 锥的数据。
2. `Structure/Equalizer.v` 或 `Pullback.v` → 用特例理解 UMP。
3. 再回 `Structure/Limit.v` 看一般定义。
4. 需要「极限 = Ran」视角时进 `Structure/Limit/Kan`（与 [10](10-monoidal-kan-ends.md) 交叉）。

下一篇：[07 Yoneda](07-yoneda.md)
