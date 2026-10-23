# 03 · 常用结构：Terminal / Initial / Cartesian / Limits

`Structure/` 描述的是：**已经有一个范畴 `C`，它 internally 还带什么普遍构造**。  
找文件时想「性质 / UMP」，不是「造一个新的范畴」（那是 `Construction/`）。

## 怎么 Require

```coq
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.

(* 或一次性拿入门子集： *)
Require Import Category.Theory.
(* Theory.v 已 Export：Cartesian、Cocartesian、Bicartesian、Terminal、Initial *)
```

## 终对象：`Structure/Terminal.v`

```coq
Class Terminal := {
  terminal_obj : C;                 (* 常记作 1 *)
  one {x} : x ~> terminal_obj;      (* 唯一的 ! : x ~> 1 *)
  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
}.
```

记号：对象作用域里的 `1` 是 `terminal_obj`；`one[x]` 显式写出实例。

短例子：任意 `f : x ~> y`，有 `one ∘ f ≈ one`（推论 `one_comp`）——因为两边都是进 `1` 的箭头。

## 初始对象：`Structure/Initial.v`

本库用**对偶**定义初始对象，而不是再抄一套字段：

```coq
Notation "'Initial' C" := (@Terminal (C^op)) …
```

于是 `0`、`zero : 0 ~> x`、`zero_unique` 都是终对象在 `C^op` 上的包装。读代码时若看到 `@Initial C`，心里换成「`C^op` 的 `Terminal`」。

## 笛卡尔（有限积）：`Structure/Cartesian.v`

二元积 + 配对 + 投影，UMP 写成双条件：

```coq
Class Cartesian := {
  product_obj : obj → obj → obj;          (* x × y *)
  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z;  (* ⟨f,g⟩，记号 f △ g *)
  exl {x y} : x × y ~> x;
  exr {x y} : x × y ~> y;
  fork_respects : …;
  ump_products … :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
}.
```

零元积（单位）来自已有的 `Terminal`（文件里用 `1` 谈 `prod_one_l` 等）。  
余积在 `Structure/Cocartesian.v`（`+`、`▽`）；两者一起是 `Bicartesian`。

## 极限：`Structure/Limit.v` 与邻居

极限建立在锥上：先有 `Structure/Cone.v`，再有 `Limit.v`。直觉：

- 形状是函子 `F : J ⟶ C`
- 极限是到 `F` 的万有锥

子目录（按需点开，不必一次读完）：

| 路径 | 用途 |
|------|------|
| `Structure/Limit/` | 有限极限、由积与等化子来、保存性、加权极限等 |
| `Structure/Equalizer.v`、`Pullback.v`、`Complete.v` | 等化子、拉回、完备性 |
| `Structure/Closed.v`、`BiCCC.v` | 闭、双笛卡尔闭 |
| `Structure/Monoidal.v` 等 | 幺半及其变体 |

「极限 vs Kan 扩张」若出现在不同目录，以父路径区分意图；需要 Kan 时再进 `Theory/Kan/`。

## 查找与命名的实用技巧

1. 先 `grep` / 仓库内搜索类型类名：`Class Terminal`、`Class Cartesian`、`Class Limit`。
2. 看文件头部的 `Require Import`，画出依赖：例如 `Cartesian` 依赖 `Terminal`。
3. 具体范畴上的实例多半在 `Instance/*.v`（如 `Sets_Terminal`、`Sets_Initial`），不要在 `Structure/` 里找「Sets 的积长什么样」。

## 最小阅读顺序

```
Terminal.v → Initial.v → Cartesian.v
        ↓
   Cocartesian.v（若需要 +）
        ↓
   Cone.v → Limit.v（若需要一般极限）
```

下一篇：[04 伴随与 Monad](04-adjunction-monad.md)
