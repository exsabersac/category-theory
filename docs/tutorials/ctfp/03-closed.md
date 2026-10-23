# 03 · 笛卡尔闭与 BiCCC

**CTFP**：Ch.9 *Function Types*。  
**DaoFP**：`6-FunctionTypes.tex`。

## 范畴论陈述

闭结构给指数对象 `y^x`（或 `x ⟹ y`）与求值/curry 的 UMP。笛卡尔闭 = 有限积 + 闭。BiCCC 再加余积，对应「和/积/函数」一整套代数数据类型。

## 编程直觉

`a -> b` 是指数；`curry` / `uncurry` 是伴随 `(- × a) ⊣ (a ⟹ -)` 的程序员说法。

## 路径与 Require

```coq
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Closed.
Require Import Category.Structure.BiCCC.    (* 或 BiCCC/ 子路径 *)
```

也查：`Structure/Cartesian/` 下与 Closed 的组合、`Structure/BiCCC.v`。

## 关键摘录

打开 `Structure/Closed.v`，定位指数与 `curry`/`eval`（字段名以文件为准）。核心形状：

- 有 `exp`（或记号 `⟹`）与 `eval : exp x y × x ~> y`；
- `curry` 满足与 `eval` 的 UMP（唯一中介态射）。

（具体 `Class` 字段以当前文件为准逐步解释，勿死记行号。）

## CoqIDE 步骤

1. 先确保已理解 [02](02-products.md) 的积。
2. 打开 `Structure/Closed.v`，解释到主 `Class`，在 Goal 里追踪 `≈`。
3. 打开 `Structure/BiCCC.v`（及子目录），看如何打包积+余积+闭。
4. 需要程序侧时看 `Instance/Coq/` 与 `Instance/Lambda/`（λ 与 CCC 桥）。

下一篇：[04 函子](04-functor.md)
