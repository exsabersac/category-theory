# CTFP / DaoFP × 本库 · 对照教程索引

把 [CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)（PDF 源：[milewski-ctfp-pdf](https://github.com/hmemcpy/milewski-ctfp-pdf)）与 [DaoFP](https://github.com/BartoszMilewski/DaoFP) 的章节进度，接到本库 `Category.*` 的正式化。Haskell 侧补充见 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)（初始代数 / Free / 函子组合 / 幺半 / Kan / Lawvere / Optics）。

**版权约定**：不摘录、不复述书中大段原文；只引**章节编号与标题**，用原创中文讲动机、定义直觉、常见坑，再落到本库 `.v` 的字段、lemma、Goal 与战术。要读原书请打开上述仓库 / PDF。

与 [../INDEX.md](../INDEX.md) 互补：那边是「怎么逛库」；这边每篇是**可独立读完的教学章**——书侧概念故事 + 编程直觉 + **带 Goal 的 Coq 证明走读**。

## 约定

- 简体中文；标识符 / `Require` / 模块名保持英文。
- `_CoqProject` 用 `-R . Category`；入口常是 `Require Import Category.Theory.`；态射相等用 `≈`（setoid）。
- **同一套材料只用一个 Coq 版本**（推荐 Coq Platform 8.20）；学到哪编到哪。
- 库自动化：`cat` / `cat_simpl` / `proper` / `equivalence`（见 `docs/AUTOMATION.md`）。新手证明里先手写 `rewrite id_left`，熟练后再让 `cat` 收尾。

## 目录

| 篇 | 文件 | 主题 | CTFP（标题） | DaoFP | 本库主路径 |
|----|------|------|--------------|-------|------------|
| 00 | [00-roadmap.md](00-roadmap.md) | 怎么读、库设计、证明习惯 | 全书对照 | 全书 | Theory / Structure / Instance |
| 01 | [01-category.md](01-category.md) | 范畴、同构、对偶 | 1.1–1.3 *Composition / Types / Great and Small* | §1–3 | `Theory/Category`、`Isomorphism`、`Morphisms`、`Opposite` |
| 02 | [02-products.md](02-products.md) | 终/始、积/余积、UMP | 1.5–1.6 *Products / ADTs* | §4–5 | `Terminal`、`Initial`、`Cartesian`、`Cocartesian` |
| 03 | [03-closed.md](03-closed.md) | 指数与 CCC | 1.9 *Function Types* | §6 | `Cartesian/Closed`、`BiCCC` |
| 04 | [04-functor.md](04-functor.md) | 函子 | 1.7–1.8 *Functors / Functoriality* | §8 | `Theory/Functor`；`Theory/Coq/Functor` |
| 05 | [05-natural.md](05-natural.md) | 自然变换 | 1.10 *Natural Transformations* | §9 | `Natural/Transformation` |
| 06 | [06-limits.md](06-limits.md) | 锥与（余）极限 | 2.2 *Limits and Colimits* | §9 Limits | `Cone`、`Limit`、`Equalizer`、`Pullback` |
| 07 | [07-yoneda.md](07-yoneda.md) | Yoneda / 可表 | 2.4–2.6 *Representable / Yoneda* | §9 Representable | `Functor/Hom/Yoneda*` |
| 08 | [08-adjunction.md](08-adjunction.md) | 伴随 | 3.2–3.3 *Adjunctions / Free-Forgetful* | §10 | `Theory/Adjunction`；`Adjunction/*` |
| 09 | [09-monad-algebra.md](09-monad-algebra.md) | Monad / EM / F-代数 | 3.4–3.6、3.8–3.9；1.4 Kleisli | §11、§13–16 | `Monad`；`Monad/Algebra`；`FAlg` |
| 10 | [10-monoidal-kan-ends.md](10-monoidal-kan-ends.md) | 幺半、Kan、End | 3.10–3.12、3.15 | §18、§20 | `Monoidal`；`Kan`；`End` |
| 11 | [11-lawvere-free.md](11-lawvere-free.md) | Lawvere 与 Free | 3.14 *Lawvere Theories*；2.3 / 3.8 | §7、§11、§15 | `Lawvere*`；`Free`、`FAlg` |
| 12 | [12-instances.md](12-instances.md) | Sets / Cat / Coq | 落地 | — | `Instance/Sets`、`Cat`、`Coq` |

可继续加厚的缺口：Applicative（DaoFP §14）、Comonad（CTFP 3.7 / DaoFP §17）、Ends→Optics（DaoFP §19）。

## 建议读法

1. [00](00-roadmap.md) → 弄清 E-category + typeclass + `≈`。
2. 环境：[../01-setup.md](../01-setup.md)。
3. 按 01→12；每篇「CoqIDE 证明走读」建议真的逐步解释一遍。
4. Haskell 直觉不够时打开 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 对应主题，再回 `.v`。
