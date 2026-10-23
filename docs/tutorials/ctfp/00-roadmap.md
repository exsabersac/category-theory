# 00 · 路线图：这套教程在干什么

**CTFP / DaoFP**：全书概念序。  
**本库**：[exsabersac/category-theory](https://github.com/exsabersac/category-theory)（上游 jwiegley）。  
**Haskell 笔记**：[haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

## 先说结论

CTFP 教你用「对象 + 箭头 + 复合」想问题；DaoFP 用 Agda 味的代码把同一套词条写一遍。本库做的是第三件事：**把这些词条变成 Coq 的 typeclass，每条定律都是可检查的证明义务**。

读完 01–12，你应能：

1. 听到「积 / 函子 / 自然变换 / 伴随 / Monad」时，立刻对应到本库哪个 `Class`、哪几个字段；
2. 在 CoqIDE 里打开对应 `.v`，看懂 Goal 里 `≈` 在比什么；
3. 分清几组易混概念（尤其 **EM 代数 ≠ F-代数**、**极限锥 ≠ 任意锥**、**闭范畴草稿 ≠ CCC**）。

## 本库设计的三块拼图

### 1. E-category：hom 是 setoid

Coq 没有商类型，不能事后说「把相等的函数当成同一个」。本库选择：每个 `hom X Y` 自带等价关系 `≈`（`homset`），复合必须 `Proper`（`compose_respects`）。这叫 **E-category**（充实到 setoid 上的范畴）。

后果你处处会碰到：

- 重写态射用 setoid rewriting，不是普通 `rewrite` 就完事；
- 定义任何「在态射上的运算」都要交 `Proper` 证明；
- 好处：`Instance/Sets.v` 可以**不靠函数外延公理**——两个函数点点 `≈` 就算同一态射。

### 2. Typeclass 字典：概念 = `Class` + 定律字段

| 你口头说的 | 库里大致落点 |
|------------|--------------|
| 范畴 | `Theory.Category.Category` |
| 函子 | `Theory.Functor.Functor` |
| 自然变换 | `Theory.Natural.Transformation.Transform` |
| 伴随 | `Theory.Adjunction.Adjunction` |
| 单子 | `Theory.Monad.Monad` |
| 终对象 / 积 / 指数 | `Structure.Terminal` / `Cartesian` / `Cartesian.Closed` |

字段分两类：**数据**（对象、态射、映射）和 **定律**（单位、结合、自然性、UMP）。证明时 Goal 几乎总是某个 `≈`。

### 3. 目录分工

```
Theory/        核心定义（Category, Functor, Monad, Adjunction, Kan, Lawvere…）
Structure/     范畴上「有某种结构」（Terminal, Cartesian, Limit, Monoidal…）
Construction/  从旧范畴造新范畴（Opposite, Product, Free, FAlg…）
Functor/       函子的种与特例（Hom, Yoneda, Applicative…）
Adjunction/    伴随的变体与定理
Monad/         Kleisli、EM、与伴随的互化
Instance/      具体范畴（Sets, Cat, Coq, FinSet…）
```

入口习惯：

```coq
Require Import Category.Theory.   (* 汇入常用 Theory *)
(* 或精确： *)
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
```

`_CoqProject` 必须有 `-R . Category`（或等价 `-Q`），否则 `Category.*` 解析失败。

## CTFP 进度 ↔ 本教程

| 你读到的大致位置 | 打开本教程 |
|------------------|------------|
| 复合、类型与函数、大小范畴 | [01](01-category.md) |
| 积与余积 | [02](02-products.md) |
| 函数类型 / 指数 | [03](03-closed.md) |
| 函子 | [04](04-functor.md) |
| 自然变换 | [05](05-natural.md) |
| 极限 | [06](06-limits.md) |
| Yoneda | [07](07-yoneda.md) |
| 伴随 | [08](08-adjunction.md) |
| Monad、Kleisli、代数 | [09](09-monad-algebra.md) |
| 充实 / End / Kan | [10](10-monoidal-kan-ends.md) |
| Lawvere、自由代数 | [11](11-lawvere-free.md) |
| 想看「真的跑在 Sets/Coq 上」 | [12](12-instances.md) |

笔记侧深耕主题（初始代数、Free、Kan、Lawvere、幺半）会在对应篇末给出链接；Optics 目前只在 End/Profunctor 处点到，未单独成篇。

## 和「只读索引」有什么不同

后面每篇都按同一骨架写满：

1. **机制**：这个概念在解决什么问题；
2. **短例子**（Haskell 风格直觉）；
3. **本库怎么编码**：字段含义、典型 Goal；
4. **易混对比**；
5. **CoqIDE 逐步操作**。

不会只丢一串 `Require` 和半截 `Class` 摘录就结束。

## CoqIDE / VsCoq 起步（30 秒）

1. 打开仓库根，确认 `_CoqProject` 含 `-R . Category`。
2. 固定 **Coq Platform 8.20**（与 `.vo` 版本一致；不要混 brew 9.3）。
3. 打开 `Theory/Category.v`，跳过文首长注释，停在 `Class Category`，逐步向下解释。
4. Goal 窗口里看到 `≈`，就明白：你在证 setoid 相等，不是 Leibniz `=`。

下一篇：[01 范畴与态射](01-category.md)
