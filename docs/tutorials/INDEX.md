# 新手教程索引

面向第一次打开本库（[exsabersac/category-theory](https://github.com/exsabersac/category-theory)）的读者。

约定：

- 正文用简体中文；**Coq 标识符、模块名、`Require` 路径一律保持英文**。
- 库根目录的 `_CoqProject` 写的是 `-R . Category`，因此模块前缀一律是 `Category.…`。
- 态射相等用 `≈`，不要用 `=`（见 [`docs/NOTATION.md`](../NOTATION.md)）。
- `.vo` 必须与当前解释器版本一致；建议同一材料固定用 **Coq Platform 8.20**（详见 [01](01-setup.md)）。

## A. 怎么逛库（工具向）

| 篇 | 文件 | 内容 |
|----|------|------|
| 00 | [00-overview.md](00-overview.md) | 仓库地图与学习路线 |
| 01 | [01-setup.md](01-setup.md) | 环境、编译、IDE |
| 02 | [02-first-walk.md](02-first-walk.md) | 从 Category → Functor → Transform 带读 |
| 03 | [03-structures.md](03-structures.md) | Terminal / Initial / Cartesian / Limit |
| 04 | [04-adjunction-monad.md](04-adjunction-monad.md) | 伴随、Monad、阅读路径 |
| 05 | [05-instances.md](05-instances.md) | Sets、Cat 等实例怎么用 |
| 06 | [06-extending.md](06-extending.md) | 自己写 Instance / 引理的约定 |

建议：00 → 01 → 02，再按需 03–06。

## B. CTFP / DaoFP × Coq（概念向）

把 Milewski CTFP / DaoFP 章节接到本库证明；顺序对齐 FP 对照表。入口：

**→ [ctfp/INDEX.md](ctfp/INDEX.md)**

| 篇 | 内容 |
|----|------|
| 00 | 路线图与完整对照表 |
| 01–03 | 范畴 → 积/和 → CCC |
| 04–07 | 函子 → 自然变换 → 极限 → Yoneda |
| 08–09 | 伴随 → Monad / EM（区分 F-代数） |
| 10–11 | 幺半·Kan·End → Lawvere / Free（重点） |
| 12 | Sets / Cat / Coq 落地 |

Haskell 侧笔记：[haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

## 相关官方文档（库内）

- [`README.md`](../../README.md)
- [`docs/NOTATION.md`](../NOTATION.md)、[`AXIOMS.md`](../AXIOMS.md)、[`INHABITATION.md`](../INHABITATION.md)、[`SIZE.md`](../SIZE.md)
- [`docs/INDEX.md`](../INDEX.md)、[`CLAUDE.md`](../../CLAUDE.md)
