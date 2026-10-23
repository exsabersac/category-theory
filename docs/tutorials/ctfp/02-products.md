# 02 · 终/始对象、积与余积

**CTFP**：Ch.5 *Products and Coproducts*，Ch.6 *Simple Algebraic Data Types*。  
**DaoFP**：`4-SumTypes.tex`、`5-ProductTypes.tex`。

## 范畴论陈述

终对象 `1`：每个对象恰有一条 `! : x ~> 1`。初始对象是对偶（本库由 `Terminal` 在 `C^op` 上定义）。二元积带投影 `exl`/`exr` 与配对 `fork`，满足 UMP。余积对偶。

## 编程直觉

`()` / `Void`；`(a,b)` / `Either a b`。UMP =「只有一种合理的构造/消除方式」。

## 路径与 Require

```coq
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.Sets.     (* 具体积 *)
```

| 文件 | 作用 |
|------|------|
| `Structure/Terminal.v` | `Class Terminal`，记号 `1`、`one` |
| `Structure/Initial.v` | `Initial := Terminal (C^op)`，`0`、`zero` |
| `Structure/Cartesian.v` | `product_obj`、`fork`、`exl`/`exr`、`ump_products` |
| `Structure/Cocartesian.v` | 余积 |
| `Instance/Sets.v`、`Instance/Coq/` | 落地到 setoid / Gallina |

## 关键摘录

```coq
Class Terminal := {
  terminal_obj : C;
  one {x} : x ~> terminal_obj;
  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
}.

Class Cartesian := {
  product_obj : obj → obj → obj where "x × y" := (product_obj x y);
  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z;
  exl {x y} : x × y ~> x;
  exr {x y} : x × y ~> y;
  ump_products {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> y × z) :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
}.
```

## CoqIDE 步骤

1. `Structure/Terminal.v` → 解释 `Class Terminal` 与 `terminal_unique`。
2. `Structure/Initial.v` → 看清对偶定义，不要重造一套公理。
3. `Structure/Cartesian.v` → 停在 `ump_products`；试读 `first`/`second`/`swap`。
4. 在 `Instance/Sets.v` 搜 `Cartesian`/`Terminal` 实例（若已编过 `.vo`），对照具体映射。

下一篇：[03 笛卡尔闭](03-closed.md)
