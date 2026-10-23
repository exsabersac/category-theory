# 00 · 路线图：CTFP / DaoFP / notes ↔ 本库

## 范畴论陈述

CTFP 按复合推进：范畴 → 积/余积 → 函子 → 自然变换 → 极限 → Yoneda → 伴随 → Monad → Kan/充实/Lawvere。DaoFP 章节文件名不同（`2-Composition` … `15-Monads` …），词条同一套。本库用 **setoid 态射 + typeclass** 收这些词条；Haskell 侧练习可对照 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

## 编程直觉

CTFP 脑内是 Haskell；本库是「哪个 `Class`、哪条定律字段」。同名概念在 Coq 里义务更全（如 `fmap_respects`）。

## Require 总入口

```coq
Require Import Category.Theory.
```

## FP 对照表（完整）

| # | 概念 | CTFP / DaoFP | 本库 | notes（若有） |
|---|------|--------------|------|----------------|
| 1 | 范畴 | 1.1–1.3；§2–3 | `Theory/Category.v`、`Isomorphism.v`、`Morphisms.v`；对偶 `Construction/Opposite.v`；程序侧 `Theory/Coq.v` | — |
| 2 | 积/和/终/始 | 1.5–1.6；§4–5 | `Structure/Terminal`、`Initial`、`Cartesian`、`Cocartesian`；实例 `Instance/Sets`、`Coq` | — |
| 3 | CCC / Closed | 1.9；§6 | `Structure/Closed.v`、`Cartesian/Closed`、`BiCCC` | — |
| 4 | 函子 | 1.7–1.8；§8 | `Theory/Functor.v`；`Functor/*`；`Theory/Coq/Functor.v` | 函子组合 |
| 5 | 自然变换 | 1.10；§9 | `Theory/Natural/Transformation.v`、`Naturality.v` | — |
| 6 | 极限 | 2.2 | `Structure/Limit*`、`Cone`、`Equalizer`、`Pullback`；`Structure/Limit/Kan` 等 | — |
| 7 | Yoneda | 2.4–2.6 | `Functor/Hom/Yoneda*`；`Theory/Universal/Element`；`Theory/Coend/Yoneda` | — |
| 8 | 伴随 | 3.2–3.3；§10 | `Theory/Adjunction.v`；`Adjunction/*` | — |
| 9 | Monad / EM | 3.4–3.6、3.8–3.9；§15–16、§11 | `Theory/Monad.v`、`Monad/Algebra.v`；**F-代数**走 `Construction/FAlg`、`Theory/Lambek`、`Theory/Adamek`（勿与 EM 代数混） | 初始代数 |
| 10 | 幺半 | （充实/张量侧） | `Structure/Monoidal*`；`Theory/Algebra/Monoid` | 幺半范畴 |
| 11 | Kan | 3.11；§20 | `Theory/Kan/Extension.v` | Kan |
| 12 | End / Profunctor | 3.10；§18–19 | `Structure/End.v`、`Coend`；`Theory/Profunctor`；`Construction/Day` | Optics（后续） |
| 13 | Lawvere | 3.14 | `Theory/Lawvere*`；`Instance/FinSet/Lawvere`（用户重点） | Lawvere |
| 14 | 初始代数 / Free | §7、§11 | `Construction/FAlg`、`Free`；`Theory/Lambek`、`Recursion`、`Adamek` | 初始代数、Free |

缺口备忘：Yoneda 深挖、Applicative（`Functor/Applicative.v`）、Comonad（`Comonad/`）、Ends→Optics。

## CoqIDE 步骤

1. 确认 `_CoqProject` 有 `-R . Category`。
2. 打开 `Theory/Category.v`，解释到 `Class Category`。
3. 按上表跳到当前 CTFP 章对应篇。

下一篇：[01 范畴](01-category.md)
