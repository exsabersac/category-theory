# CTFP / DaoFP × 本库 · 对照教程索引

把 [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)（PDF：[milewski-ctfp-pdf](https://github.com/hmemcpy/milewski-ctfp-pdf)）与 [DaoFP](https://github.com/BartoszMilewski/DaoFP) 的章节进度，接到本库 `Category.*` 的正式化。概念顺序对齐队友 FP 的对照表；Haskell 侧笔记见 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)（初始代数 / Free / 函子组合 / 幺半 / Kan / Lawvere / Optics）。

**不**摘录书中正文；只引章节标题/编号，自述概念，再落到 `.v`。

与 [../INDEX.md](../INDEX.md) 互补：那边「怎么逛库」，这边「CTFP 概念 → Coq 路径」。

## 约定

- 简体中文；标识符 / `Require` / 模块名保持英文。
- `-R . Category` → `Require Import Category.…`；态射相等用 `≈`。
- 固定 Coq Platform 8.20；学到哪编到哪。

## 目录（按 FP 概念序）

| 篇 | 文件 | CTFP / DaoFP 锚点 | 本库 |
|----|------|-------------------|------|
| 00 | [00-roadmap.md](00-roadmap.md) | 全书对照 | 总表 + notes 链接 |
| 01 | [01-category.md](01-category.md) | CTFP 1.1–1.3；DaoFP §2–3 | `Theory/Category`、`Isomorphism`、`Morphisms`、`Opposite`；`Theory/Coq` |
| 02 | [02-products.md](02-products.md) | CTFP 1.5–1.6；DaoFP §4–5 | `Structure/Terminal`、`Initial`、`Cartesian`、`Cocartesian`；`Instance/Sets` |
| 03 | [03-closed.md](03-closed.md) | CTFP 1.9；DaoFP §6 | `Structure/Closed`、`Cartesian/Closed`、`BiCCC` |
| 04 | [04-functor.md](04-functor.md) | CTFP 1.7–1.8；DaoFP §8 | `Theory/Functor`；`Functor/*`；`Theory/Coq/Functor` |
| 05 | [05-natural.md](05-natural.md) | CTFP 1.10；DaoFP §9 | `Theory/Natural/Transformation`、`Naturality` |
| 06 | [06-limits.md](06-limits.md) | CTFP 2.2 | `Structure/Limit*`、`Cone`、`Equalizer`、`Pullback`；Kan 极限路径 |
| 07 | [07-yoneda.md](07-yoneda.md) | CTFP 2.4–2.6 | `Functor/Hom/Yoneda*`；`Theory/Universal/Element`；`Theory/Coend/Yoneda` |
| 08 | [08-adjunction.md](08-adjunction.md) | CTFP 3.2–3.3；DaoFP §10 | `Theory/Adjunction`；`Adjunction/*` |
| 09 | [09-monad-algebra.md](09-monad-algebra.md) | CTFP 3.4–3.6、3.8–3.9；DaoFP §11、§15–16 | `Theory/Monad`；`Monad/Algebra`；区分 `Construction/FAlg` / Lambek / Adamek |
| 10 | [10-monoidal-kan-ends.md](10-monoidal-kan-ends.md) | CTFP 3.10–3.12；DaoFP §18、§20–21 | 幺半 / Kan / End·Profunctor·Day |
| 11 | [11-lawvere-free.md](11-lawvere-free.md) | CTFP 3.14；DaoFP 代数侧 | `Theory/Lawvere*`；`FinSet/Lawvere`；Free / 初始代数 |
| 12 | [12-instances.md](12-instances.md) | 落地 | `Instance/Sets`、`Cat`、`Coq` |

已知可后续加厚的缺口：Yoneda 深挖、Applicative、Comonad、Ends→Optics（notes 里 Optics 专题）。

## 建议读法

1. 扫 [00](00-roadmap.md)，对照你读到的 CTFP/DaoFP 章。
2. 环境：[../01-setup.md](../01-setup.md)。
3. 每篇五步：**陈述 → 短直觉 → 路径/Require → 短摘录 → CoqIDE**。
4. Haskell 直觉不够时，打开 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 对应主题，再回 `.v`。
