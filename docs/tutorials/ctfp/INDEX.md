# CTFP / DaoFP × 本库 · 对照教程索引

把 [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)（PDF：[milewski-ctfp-pdf](https://github.com/hmemcpy/milewski-ctfp-pdf)）与 [DaoFP](https://github.com/BartoszMilewski/DaoFP) 的章节进度，接到本库 `Category.*` 的正式化。Haskell 侧补充直觉见 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)（初始代数 / Free / 函子组合 / 幺半 / Kan / Lawvere / Optics）。

**不**摘录书中正文；只引章节标题/编号，自述概念机制，再落到 `.v` 的字段与证明义务。

与 [../INDEX.md](../INDEX.md) 互补：那边是「怎么逛库」；这边每篇都是**可独立读懂**的主题教程（概念 → 直觉 → 库内机制 → 易混对比 → CoqIDE）。

## 约定

- 简体中文；标识符 / `Require` / 模块名保持英文。
- `_CoqProject` 用 `-R . Category`，入口常是 `Require Import Category.Theory.`；态射相等用 `≈`（setoid）。
- **同一套材料只用一个 Coq 版本**（推荐 Coq Platform 8.20）；学到哪编到哪。
- 讲解节奏：先陈述机制，再给短例子；不堆教科书式公式墙。

## 目录

| 篇 | 文件 | 主题 | CTFP / DaoFP（仅编号） | 本库主路径 |
|----|------|------|------------------------|------------|
| 00 | [00-roadmap.md](00-roadmap.md) | 怎么读这套、库设计总图 | 全书对照 | Theory / Structure / Instance |
| 01 | [01-category.md](01-category.md) | 范畴、同构、对偶 | CTFP 1.1–1.3；DaoFP §2–3 | `Theory/Category`、`Isomorphism`、`Morphisms`、`Opposite` |
| 02 | [02-products.md](02-products.md) | 终/始、积/余积、UMP | CTFP 1.5–1.6；DaoFP §4–5 | `Structure/Terminal`、`Initial`、`Cartesian`、`Cocartesian` |
| 03 | [03-closed.md](03-closed.md) | 指数对象与 CCC | CTFP 1.9；DaoFP §6 | `Structure/Cartesian/Closed`、`BiCCC` |
| 04 | [04-functor.md](04-functor.md) | 函子三定律 | CTFP 1.7–1.8；DaoFP §8 | `Theory/Functor`；`Theory/Coq/Functor` |
| 05 | [05-natural.md](05-natural.md) | 自然变换与自然性方块 | CTFP 1.10；DaoFP §9 | `Theory/Natural/Transformation` |
| 06 | [06-limits.md](06-limits.md) | 锥与（余）极限 | CTFP 2.2 | `Structure/Cone`、`Limit`、`Equalizer`、`Pullback` |
| 07 | [07-yoneda.md](07-yoneda.md) | Yoneda 引理与可表 | CTFP 2.4–2.6 | `Functor/Hom/Yoneda*` |
| 08 | [08-adjunction.md](08-adjunction.md) | 伴随三种面孔 | CTFP 3.2–3.3；DaoFP §10 | `Theory/Adjunction`；`Adjunction/*` |
| 09 | [09-monad-algebra.md](09-monad-algebra.md) | Monad / EM / F-代数（分清） | CTFP 3.4–3.6、3.8–3.9；DaoFP §11、§15–16 | `Theory/Monad`；`Monad/Algebra`；`Construction/FAlg` |
| 10 | [10-monoidal-kan-ends.md](10-monoidal-kan-ends.md) | 幺半、Kan、End/Profunctor | CTFP 3.10–3.12；DaoFP §18、§20 | `Structure/Monoidal`；`Theory/Kan`；`Structure/End` |
| 11 | [11-lawvere-free.md](11-lawvere-free.md) | Lawvere 理论与 Free/初始代数 | CTFP 3.14；代数侧 | `Theory/Lawvere*`；`Construction/Free`、`FAlg` |
| 12 | [12-instances.md](12-instances.md) | Sets / Cat / Coq 落地 | 落地章 | `Instance/Sets`、`Cat`、`Coq` |

已知可继续加厚的缺口（文中已点到但不单独成篇）：Applicative、Comonad 深挖、Ends→Optics。

## 建议读法

1. 先读 [00](00-roadmap.md)，弄清本库「E-category + typeclass」在干什么。
2. 环境：[../01-setup.md](../01-setup.md)。
3. 按 01→12 推进；每篇末尾的 CoqIDE 步骤建议真的在编辑器里走一遍。
4. Haskell 直觉不够时，打开 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 对应主题，再回 `.v`。
