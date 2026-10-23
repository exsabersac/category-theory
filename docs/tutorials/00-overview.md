# 00 · 仓库概览与学习路线

先建立地图，再进具体文件。本库大约一千多个 `.v`，不要从上到下读。

## 一句话

用 **setoid 上的态射**（相等是 `≈`，不是 `=`）把范畴论编进 Coq；模块前缀是 `Category`（见根目录 `_CoqProject` 的 `-R . Category`）。

入口一句话：

```coq
Require Import Category.Theory.
```

这会拉入范畴、同构、函子、自然变换、伴随，以及 Terminal / Initial / Cartesian / Cocartesian / Bicartesian（见根目录 `Theory.v`）。

## 顶层目录怎么逛

| 目录 | 干什么 | 新手先看 |
|------|--------|----------|
| `Theory/` | 核心定义：Category、Functor、Natural、Adjunction、Monad、Kan… | `Category.v`、`Functor.v`、`Natural/Transformation.v`、`Adjunction.v`、`Monad.v` |
| `Structure/` | 范畴**内部**结构（终对象、积、极限、闭、幺半、Topos…） | `Terminal.v`、`Initial.v`、`Cartesian.v`、`Limit.v` |
| `Construction/` | 在旧范畴上**造新范畴**（对偶、逗号、切片、Arrow、Free…） | `Opposite.v`、`Comma.v`（需要时再进） |
| `Functor/`、`Natural/`、`Adjunction/`、`Monad/`、`Comonad/` | 各概念的「种」与定理（保持结构的函子、伴随连续性、Kleisli…） | 跟完 Theory 后再按主题进 |
| `Instance/` | 具体范畴：`Sets`、`Cat`、`Coq`、`FinSet`、代数范畴… | `Sets.v`、`Cat.v` |
| `Lib/` | Setoid、tactic（`cat`、`proper`…） | 证明卡住时再查 |
| `docs/` | 记号、公理、索引、**本教程** | `tutorials/`、`NOTATION.md` |
| `Test/`、`Tools/`、`Solver/`、`doc/plan/` | 测试、工具、长期计划 | 新手可略 |

命名习惯：同名文件很多，**父路径表达意图**。例如极限既有 `Structure/Limit.v`，也有与 Kan 扩张相关的路径；逗号范畴下还有 `Construction/Comma/Natural/Transformation.v`。找东西时先想「这是结构、构造，还是某概念的变种」，再对目录。

## 学习路线（实用版）

```
① 环境能编译单个 .v
        ↓
② Theory：Category → Functor → Transform
        ↓
③ Structure：Terminal / Initial / Cartesian
        ↓
④ Instance：Sets（具体对象与箭头）
        ↓
⑤ Adjunction → Monad（Theory 定义 + Monad/Adjunction.v）
        ↓
⑥ 按需：Limit、Closed、Construction/Opposite、Cat
```

不必先读完 Mac Lane。本库每个核心文件文首都有动机注释和 nLab / 论文链接，卡住时往回看那一段即可。

## 三条硬习惯

1. **同一套材料只用一个 Coq 版本**（推荐 Platform 8.20）。用 9.x 编出的 `.vo` 不能交给 8.20 的 CoqIDE，反之亦然。
2. **不要一上来整库 `make`**。依赖多、文件多；日常「学到哪编到哪」。
3. **Require 用库前缀**：`Category.Theory.Category`，不要写相对路径当模块名。

下一篇：[01 环境搭建与编译](01-setup.md)
