# 11 · Lawvere 理论与初始代数 / Free（重点）

**CTFP**：Ch.14 *Lawvere Theories*；代数侧亦见 Ch.8–9。  
**DaoFP**：`11-Algebras.tex`、`7-Recursion.tex`。  
**notes**：Lawvere、初始代数、Free——**用户关注点**。

## 范畴论陈述

Lawvere 理论：有限积范畴呈现代数理论；模型 = 保积函子到（例如）Sets。  
初始 F-代数：`μF`，Lambek 定理说结构映射是同构；Adamek：在合适假设下由迭代余极限构造。Free 构造在 `Construction/Free*`。

## 编程直觉

「接口 = 理论，实现 = 模型」。`Free f` / 初始代数 = 语法树；递归图式 = catamorphism（notes）。

## 路径与 Require

```coq
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Instance.FinSet.Lawvere.  (* 若路径存在；按仓库浏览 *)
Require Import Category.Construction.FAlg.
Require Import Category.Construction.Free.
Require Import Category.Theory.Lambek.
Require Import Category.Theory.Recursion.
Require Import Category.Theory.Adamek.
```

先 `ls Theory/Lawvere Instance/FinSet` 确认当前树中的准确文件名。

## 关键摘录

```coq
(* Theory/Lawvere.v *)
Class LawvereTheory : Type := { ... }.
```

模型侧见 `Theory/Lawvere/Model.v`。F-代数同志：`Construction/FAlg.v` 的 `FAlgHom`。与 [09](09-monad-algebra.md) 对照：Lawvere/F-代数讲的是**签名函子**，EM 讲的是**单子**。

## CoqIDE 步骤

1. `Theory/Lawvere.v` → `LawvereTheory` 字段；再开 `Model.v`。
2. `Instance/FinSet/` 下找 Lawvere 相关实例（用户重点落地）。
3. `Construction/FAlg.v` + `Theory/Lambek.v`：读定理语句即可。
4. `Construction/Free.v`（及子目录）与 notes「Free」对照一张表：语法 / 遗忘 / 单位。
5. `Theory/Adamek.v`、`Recursion.v` 作选读。

下一篇：[12 Instance 落地](12-instances.md)
