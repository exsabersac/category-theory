# 01 · 环境搭建与编译

目标：在本机打开任意一个 `.v`，逐步解释能过，且 `Require` 找得到 `Category.…`。

## 版本建议

- 上游声明支持 Coq **8.19–8.20** 与 Rocq **9.0–9.1**，并依赖 **coq-equations**（约 1.2–1.3）。
- 日常学习建议固定 **Coq Platform ~8.20**（含 CoqIDE）。若本机还有 Homebrew 的 Rocq/Coq 9.x，**不要混用同一批 `.vo`**。
- 判据：`.vo` 里的版本号必须与当前 `coqc` / IDE 一致（8.20 与 9.3 互不兼容）。换版本就 `make clean` 或删掉相关 `.vo` 再编。

查看当前编译器：

```bash
coqc -v
which coqc
```

用 Platform 时，确认 `PATH` / IDE 设置指向 Platform 的 `…/Contents/Resources/bin/coqc`，而不是另一套 brew 的。

## `_CoqProject` 在说什么

库根目录：

```
-R . Category
```

含义：当前仓库根映射为逻辑路径前缀 **`Category`**。因此：

| 磁盘路径 | Require |
|----------|---------|
| `Theory/Category.v` | `Category.Theory.Category` |
| `Structure/Terminal.v` | `Category.Structure.Terminal` |
| `Instance/Sets.v` | `Category.Instance.Sets` |

你自己的项目若要依赖本库，在对方的 `_CoqProject` 里写：

```
-R <本库绝对或相对路径> Category
```

## 三种编译方式

### 1）单文件（推荐入门）

在仓库根：

```bash
coqc -R . Category Theory/Category.v
```

有依赖时，先编依赖，或让 IDE 按 `_CoqProject` 自动处理。`Category.Lib` 几乎处处需要，通常会先被拉起。

### 2）CoqIDE / VsCoq

- 用 **打开目录 = 仓库根**，保证读到根上的 `_CoqProject`。
- CoqIDE：打开章 → 逐步向下解释 → 看 Goal；必要时 Compile Buffer。卡住就向上回退。
- VsCoq Legacy：工作区指向本库根；解释器路径与用来编 `.vo` 的 `coqc` 必须同一版本。

### 3）整库 `make` / Nix

```bash
# Nix（上游推荐；默认偏 Rocq 9.1）
nix build
nix build .#category-theory_8_20
nix develop   # 再 make

# 已有合适 coqc + equations 时
make
make clean
```

**新手注意**：整库很大，第一次全编耗时长；缺 equations、版本不对时会大面积失败。入门阶段用「单文件 / IDE 逐步」即可。上游 `make` 还会跑 lint、format 等目标，见 `README.md`。

## 最小自测

在仓库根新建临时文件（不必提交），例如 `scratch/Hello.v`：

```coq
Require Import Category.Theory.

(* Theory.v 已导出 Category / Functor / Transform / Adjunction
   以及 Terminal、Initial、Cartesian 等 *)
Check Category.
Check Functor.
Check @Terminal.
```

用 IDE 打开并解释，或：

```bash
coqc -R . Category scratch/Hello.v
```

能 `Check` 出类型，说明路径与版本基本正确。

## 常见坑

| 现象 | 处理 |
|------|------|
| `Cannot find library Category.Theory…` | 工作目录不是库根，或没加 `-R . Category` / `_CoqProject` 未加载 |
| `.vo` 版本不匹配 / compiled with … | 清 `.vo`，只用当前 IDE 那套 `coqc` 重编 |
| 缺 `Equations` | 安装与 Coq 版本匹配的 `coq-equations`；或用 `nix develop` |
| 整库 `make` 中途挂掉 | 先保证单文件能过；再查版本与 equations，不要混用 8.20 / 9.x 产物 |

下一篇：[02 第一个证明游走](02-first-walk.md)
