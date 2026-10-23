# 10 · 幺半、Kan 扩张、End / Profunctor

**CTFP**：Ch.10–12 *Ends and Coends* / *Kan Extensions* / *Enriched Categories*。  
**DaoFP**：`18-Ends.tex`、`20-Kan.tex`、`21-Enrichment.tex`。  
**notes**：幺半范畴、Kan；Optics 后续。

## 范畴论陈述

- **幺半范畴**：张量 ⊗、单位、结合子/单位子（及融贯）。
- **Kan 扩张**：左/右 Kan；极限/余极限与伴随的许多定理可写成 Kan。
- **(Co)end**：Dinatural 族的泛对象；profunctor 与 Day 卷积常用 end/coend 公式。

## 编程直觉

Applicative ≈ 松弛幺半函子（程序侧见 `Functor/Applicative.v`，本篇不展开）。`foldMap` / 加权列极限常是 Kan 口号。Lens 的 profunctor 编码靠 end——见 notes Optics，此处只指路。

## 路径与 Require

```coq
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.          (* 若在 Structure；亦查 Theory/Coend *)
Require Import Category.Theory.Profunctor.
Require Import Category.Construction.Day.
```

| 主题 | 路径 |
|------|------|
| 幺半 | `Structure/Monoidal*`、`Premonoidal*`、`Binoidal*` |
| Monoid 对象 | `Theory/Algebra/Monoid`、`Structure/Monoid.v` |
| Kan | `Theory/Kan/Extension.v`（`LeftKan`/`RightKan`） |
| End/Coend | `Structure/End.v`、`Coend`；`Theory/Coend/` |
| Profunctor / Day | `Theory/Profunctor*`、`Construction/Day.v`、`Construction/Profunctor/` |

## 关键摘录

```coq
(* Theory/Kan/Extension.v 形状 *)
Class RightKan := { ... }.
Class LeftKan  := { ... }.
```

打开文件看 `ran`/`lan` 与泛性质字段；End 文件找 wedge + 泛性质。

## CoqIDE 步骤

1. 若只为 CTFP 主线：扫 `Theory/Kan/Extension.v` 的 `LeftKan`/`RightKan` 类头即够。
2. 幺半：从 `Structure/Monoidal.v` 类头读起，结合 notes「幺半范畴」。
3. End：`Structure/End.v` + `Theory/Profunctor.v`；Day 卷积打开 `Construction/Day.v` 文首。
4. Optics / Tambara：标为缺口，链到 haskell-algebra-notes。

下一篇：[11 Lawvere 与 Free](11-lawvere-free.md)
