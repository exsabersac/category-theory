# 12 · 实例落地：Sets、Cat、Coq

前面 01–11 是**词典**；本篇看词典如何打在三个最常用的具体范畴上。读完应能：在 `Instance/` 里找到实例、看懂 `Program Instance` 在交哪些义务、把抽象字段对回具体函数。

## 总览

| 实例 | 路径 | 对象直觉 | 态射直觉 |
|------|------|----------|----------|
| **Sets** | `Instance/Sets.v` | setoid（集合+等价） | 尊重等价的映射 |
| **Cat** | `Instance/Cat.v` | 范畴 | 函子（相等偏自然同构） |
| **Coq** | `Instance/Coq.v` 及子树 | Coq 类型 | Gallina 函数 |
| **FinSet** | `Instance/FinSet.v` 等 | 有限集 | 函数；接 Lawvere |
| **Fun** | `Instance/Fun.v` | 函子 | 自然变换 = `[C,D]` |

还有 Ab、Field、Lambda… 按需浏览；新手先打通 Sets → Coq → Cat。

---

## A. `Instance/Sets.v`

### 机制

对象不是裸 `Type`，而是 **Setoid**：carrier + 等价关系。  
态射是 `Proper` 的函数；两个态射 `≈` 当点点 `≈`（陪域等价）。  
因此：**函数外延不必当公理加进来**——外延性写进了 `homset`。

这是本库选 E-category 的最大回报之一。

### 你要在文件里找什么

1. `Category` 实例：`obj` / `hom` / `id` / `compose` 各是什么；  
2. `Terminal` / `Cartesian` / `Closed`（若有）如何用具体类型构造；  
3. 任意 `Proper` Obligation——感受 setoid 义务长什么样。

### 典型 Goal

`f ≈ g` 在 Sets 里常变成 `∀ x, f x ≈ g x`；再对 carrier 的等价关系重写。

---

## B. `Instance/Coq.v` 与 `Theory/Coq/`

### 两条线

- **`Instance/Coq*`**：把「Coq 类型与函数」做成 `Category` 等实例，供抽象定理特化；  
- **`Theory/Coq/*`**：程序员风格的 `Functor`/`Monad`/`Applicative`… 类，不一定走完整 E-category 重型装备。

学抽象定义：回 `Theory/Functor.v`。  
想写 Gallina 感的 fmap/bind：看 `Theory/Coq/Functor.v`、`Theory/Coq/Monad.v` 与 `Instance/Coq/Monad.v`。

### 短例子

```coq
(* 直觉对应 *)
(* fmap  ~ Theory/Coq/Functor *)
(* >>=   ~ Theory/Coq/Monad  *)
```

注意：Coq 类型范畴的等价性、函数外延、命题外延等问题，会决定哪些「Haskell 里显然」的式子能原样证明。卡住时看该实例选的 `homset` 是什么。

---

## C. `Instance/Cat.v` 与 `Instance/Fun.v`

- **Cat**：对象是（小）范畴，态射是函子。  
- **Fun / `[C,D]`**：对象是函子 `C⟶D`，态射是自然变换。

这里最常见的概念坑来自 [04](04-functor.md)：函子相等默认不是严格点点相等。读 `Cat` 里范畴定律证明时，会看到自然同构或 `Functor_Setoid` 的 `equiv`。

`Fun` 是自然变换垂直复合的家；跟 [05](05-natural.md) 对照读。

---

## D. 和 Structure 实例的配合

抽象类在 `Structure/*`，具体存在性在 `Instance/*`：

```text
Structure/Cartesian.v     定义「何谓有积」
Instance/Sets.v           给出 Sets 有积
Functor/Structure/...     要求函子保积
```

证明「某构造保极限」时，经常：在抽象层写定理，再在 Sets/Coq 实例上拿到可计算/可展示的箭头。

FinSet + `Instance/FinSet/Lawvere.v` 接 [11](11-lawvere-free.md)。

---

## 易混对比

| 易混 | 分清 |
|------|------|
| `Instance/Coq` vs `Theory/Coq` | 前者偏「范畴实例」；后者偏「程序类」 |
| Sets vs Coq | Sets 强调 setoid；Coq 实例直接打在类型上，义务不同 |
| Cat 的态射 | 是函子，不是「范畴之间的函数」口头禅 |
| `≈` 在各实例 | 都叫 `≈`，语义由该实例 `homset` 决定 |

---

## CoqIDE 步骤（建议半日路线）

1. 打开 `Instance/Sets.v`，定位 `Category` 实例；逐步解释至 `compose_respects`。  
2. 在同一文件找 `Terminal` 或积相关实例，对照 [02](02-products.md) 字段。  
3. 打开 `Instance/Coq.v`，对比 `obj`/`hom` 与 Sets 的差异。  
4. 打开 `Theory/Coq/Monad.v`，写一个小 `Require` 试验文件（可选）只 `Check` 类名。  
5. 打开 `Instance/Fun.v`，确认态射是 `Transform`。  
6. 打开 `Instance/Cat.v` 浏览定义；遇到 `Functor_Setoid` 就回 [04](04-functor.md)。  
7. （选）`Instance/FinSet/Lawvere.v` + 笔记 Lawvere demo。

---

## 学完 00–12 之后做什么

1. 带着 CTFP/DaoFP 当前章节，回点 [INDEX](INDEX.md) 对应篇，对着 `.v` 做笔记。  
2. 在 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 补 Yoneda / Applicative / Comonad / Optics 缺口。  
3. 环境与逛库总览：[../01-setup.md](../01-setup.md)、[../INDEX.md](../INDEX.md)。  
4. 真要扩展库：读 [../06-extending.md](../06-extending.md)（若在初学教程树中）。

回到总索引：[INDEX.md](INDEX.md)
