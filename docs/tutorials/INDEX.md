# 新手教程索引

面向第一次打开本库（[exsabersac/category-theory](https://github.com/exsabersac/category-theory)）的读者：讲清**怎么逛、怎么编、怎么 Require、怎么顺着定义往下读**，不讲范畴论教科书。

约定：

- 正文用简体中文；**Coq 标识符、模块名、`Require` 路径一律保持英文**。
- 库根目录的 `_CoqProject` 写的是 `-R . Category`，因此模块前缀一律是 `Category.…`。
- 态射相等用 `≈`，不要用 `=`（见 [`docs/NOTATION.md`](../NOTATION.md)）。
- `.vo` 必须与当前解释器版本一致；建议同一材料固定用 **Coq Platform 8.20**（详见 [01](01-setup.md)）。

## 目录

| 篇 | 文件 | 内容 |
|----|------|------|
| 00 | [00-overview.md](00-overview.md) | 仓库地图与学习路线 |
| 01 | [01-setup.md](01-setup.md) | 环境、编译、IDE |
| 02 | [02-first-walk.md](02-first-walk.md) | 从 Category → Functor → Transform 带读 |
| 03 | [03-structures.md](03-structures.md) | Terminal / Initial / Cartesian / Limit |
| 04 | [04-adjunction-monad.md](04-adjunction-monad.md) | 伴随、Monad、阅读路径 |
| 05 | [05-instances.md](05-instances.md) | Sets、Cat 等实例怎么用 |
| 06 | [06-extending.md](06-extending.md) | 自己写 Instance / 引理的约定 |

## 建议阅读顺序

1. 扫一眼 [00](00-overview.md)，知道各大目录干什么。
2. 按 [01](01-setup.md) 把某个 `.v` 在 IDE 里跑通（不必整库 `make`）。
3. 跟 [02](02-first-walk.md) 打开三个核心文件，看清类型类字段。
4. 需要积 / 极限时看 [03](03-structures.md)；需要伴随 / 单子时看 [04](04-adjunction-monad.md)。
5. 想在具体范畴里试手，看 [05](05-instances.md)；要贡献代码看 [06](06-extending.md)。

## 相关官方文档（库内）

- [`README.md`](../../README.md) — 构建方式、库结构总览、主要记号
- [`docs/NOTATION.md`](../NOTATION.md) — 记号速查
- [`docs/AXIOMS.md`](../AXIOMS.md) — 公理审计（核心理论 vs 实例层）
- [`docs/INHABITATION.md`](../INHABITATION.md) — 哪些旗舰结果有树内见证
- [`docs/SIZE.md`](../SIZE.md) — 宇宙与大小
- [`docs/INDEX.md`](../INDEX.md) — 关键文件与概念的分项索引
- [`CLAUDE.md`](../../CLAUDE.md) — 架构与开发备忘
