# 05 · Instance 实例库怎么用

`Instance/` 放的是**具体范畴**（以及它们身上的结构实例）。Theory / Structure 提供「接口」，这里提供「实现」。

## 两个必看例子

### `Sets`：`Instance/Sets.v`

```coq
Require Import Category.Instance.Sets.

(* 对象：SetoidObject；箭头：尊重 ≈ 的 setoid 映射 *)
Check Sets.                 (* : Category *)
Check Sets_Terminal.        (* Sets 有终对象 *)
Check Sets_Initial.
```

要点：

- 这是 **setoid 的范畴**，不是「裸 Coq `Type` 的相等范畴」。箭头相等按陪域的 `≈` 逐点比较，从而许多地方不必假定函数外延公理。
- 文件里还挂了积 / 幺半等结构实例；需要什么再往下搜 `Sets_` 前缀。
- `Theory/Adjunction.v` 依赖 `Sets`，因为伴随的 hom 集同构落在这个范畴里。

### `Cat`：`Instance/Cat.v`

```coq
Require Import Category.Instance.Cat.

Check Cat.   (* 对象是 Category，箭头是 Functor *)
```

字段直觉：

| Cat 的字段 | 含义 |
|------------|------|
| `obj` | `Category` |
| `hom` | `Functor` |
| `id` | 恒等函子 `Id` |
| `compose` | 函子复合 `Compose` |
| 相等 | `Functor_Setoid`（自然同构意义下） |

所以在 `Cat` 里谈「两个函子相等」，默认不是严格相等。

## 目录里还有什么（抽样）

| 文件 / 子目录 | 大致内容 |
|---------------|----------|
| `Coq.v`、`Theory/Coq/` | 面向编程的 Coq 类型与函数 |
| `FinSet/`、`Ens.v`、`Ord/` | 有限集、集合变体、序 |
| `Ab.v`、`Mon/`、`Grp/`、`Ring` 等 | 代数范畴 |
| `Fun/`、`Adj/` | 函子范畴、伴随相关实例 |
| `Proset/`、`Rel` 等 | 预序、关系 |
| `ZX.v` | ZX-calculus（库内少有的 `Parameter` 相位，见 `docs/AXIOMS.md`） |

完整清单以目录为准；`docs/INDEX.md` 对部分 headline 文件有测量型 bullet。

## 典型用法模式

1. **只做抽象证明**：`Require Import Category.Theory`，在带 `Context `{C : Category}`` 的节里写。
2. **需要具体箭头**：再 `Require Import Category.Instance.Sets`（或 `Cat`），用 `Sets` 上的实例放电。
3. **搜索实例**：

```coq
Search Terminal Sets.
Search Cartesian Sets.
```

或在仓库里搜 `Program Instance Sets_` / `Instance Cat`。

## 公理意识（避免误解 README）

- **核心理论**目标是无额外公理；审计见 `docs/AXIOMS.md`。
- **实例层**（尤其 `Instance/`、`Theory/Coq/`）可能依赖 stdlib 公理——文档会写明。「Closed under the global context」只对审计列表里的定义成立，不是「每一个 `.v` 都零公理」。

## 小练习

```coq
Require Import Category.Theory.
Require Import Category.Instance.Sets.

(* 1 在 Sets 里是什么？ *)
Check (1 : obj[Sets]).

(* 从任意 setoid 对象到 1 的箭头 *)
Check (@one Sets Sets_Terminal).
```

在 IDE 里逐步解释，看看 `one` 的类型是否符合你对终对象的直觉。

下一篇：[06 如何扩展](06-extending.md)
