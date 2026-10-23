# 02 · 终/始对象、积与余积

**CTFP**：约 1.5–1.6（积与余积相关章）。  
**DaoFP**：`4-SumTypes`、`5-ProductTypes` 一带。

## 这个概念在干什么

「配对」「二选一」「空」「单元」这些日常结构，范畴论不用「里面有几个字段」来定义，而用 **普遍性质（UMP）**：

> 给出想要的投影/嵌入行为之后，存在唯一的中介箭头去完成图。

终对象、积、拉回、极限……都是同一句话的不同形状。本篇先掌握最小的几块：`Terminal`、`Initial`、`Cartesian`、`Cocartesian`。

## 终对象与初始对象

### 机制

- **终对象** `1`：对每个 `x`，有且仅有一条 `! : x ~> 1`（在 `≈` 下唯一）。
- **初始对象** `0`：对偶——对每个 `x` 有且仅有 `¡ : 0 ~> x`。

在 **Set**：

- 终对象 ≈ 单元素集 `()` / `unit`；
- 初始对象 ≈ 空集 `Void` / `Empty`。

「有且仅有」在本库拆成：**存在性数据** + **唯一性定律**。

### 本库：`Structure/Terminal.v`

```coq
Class Terminal := {
  terminal_obj : C;
  one {x} : x ~> terminal_obj;           (* ! : x ~> 1 *)
  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
}.
```

记号：对象侧常写 `1`，态射侧 `one` / `one[x]`。

立刻能用的推论：

- `one ∘ f ≈ one`（进终对象的箭头合成后还是那条唯一箭头）；
- `const f := f ∘ one`：经 `1` 分解的「常值」态射；
- `terminal_unique`：两个终对象之间有（唯一）同构。

初始对象在 `Structure/Initial.v`，可由对偶从终对象导出；读时对照 `0` 与 `zero` 命名。

### 编程直觉

```haskell
-- 终：只有一个值
data () = ()

-- 初始：没有值；absurd :: Void -> a
```

全局元（element）常写成 `1 ~> X`：从单元进 `X` 的箭头 ≈ 「挑一个点」。这在后来谈生成元、Yoneda 时还会出现。

## 二元积：`Structure/Cartesian.v`

### 机制

对象 `x × y` 配上投影 `exl : x×y ~> x`、`exr : x×y ~> y`，使得：对任意 `f : a ~> x`、`g : a ~> y`，存在唯一 `⟨f,g⟩ : a ~> x×y` 满足

```text
exl ∘ ⟨f,g⟩ ≈ f
exr ∘ ⟨f,g⟩ ≈ g
```

本库把 UMP 写成**双条件** `ump_products`：

```coq
Class Cartesian := {
  product_obj : obj → obj → obj where "x × y" := (product_obj x y);
  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z;  (* ⟨f,g⟩，记号 △ *)
  exl {x y} : x × y ~> x;
  exr {x y} : x × y ~> y;
  fork_respects : … Proper …;
  ump_products {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> y × z) :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
}.
```

读法：

- 左→右：配对确实投影回 `f`、`g`（存在性）；
- 右→左：任何同时满足两投影方程的 `h` 都等于 `fork f g`（唯一性）。

派生等式（文件后文 corollary）：`exl_fork`、`exr_fork`、`fork_exl_exr`（η：`⟨exl,exr⟩ ≈ id`）等。证明积相关引理时，优先找这些，而不是每次展开 `ump_products`。

`first` / `second`：只改积的一侧，`first f = f × id` 的形状，后面 CCC 的 `ump_exponents` 会用到。

另有谓词版 `IsCartesianProduct`：不捆绑「范畴上全局选好的积」，只说「`z` 是 `x,y` 的一个积」。做「在同构下唯一」时有用。

### 短例子

```haskell
-- 积
fst :: (a, b) -> a
snd :: (a, b) -> b
(-- | 配对) (&&&) :: (a -> b) -> (a -> c) -> a -> (b, c)
```

UMP 翻译成程序员语言：若你有 `h : a -> (b,c)`，则 `h` 本质就是 `(fst.h, snd.h)`；没有另一种「秘密配对方式」。

## 余积（和）：`Structure/Cocartesian.v`

对偶于积：

- 对象 `x + y`；
- 注入 `inl` / `inr`；
- 余配对（case 分析）`f ▽ g`；
- UMP：出 `x+y` 的箭头由两臂唯一决定。

Haskell：`Either a b`、`Left`/`Right`、`either f g`。  
Sets 里余积是不交并；在别的范畴可能是「更自由的和」。

## 和极限的关系（预告）

- 终对象 = **空图**的极限；
- 积 = **离散两点图**的极限；
- 等化子、拉回 = 别的形状的极限。

所以 [06](06-limits.md) 不是新宗教，而是把本篇 UMP 话术统一起来。先把 `Terminal`/`Cartesian` 的字段摸熟，读 `Cone`/`Limit` 会轻松很多。

## 易混对比

| 易混 | 分清 |
|------|------|
| 积 vs 张量 `⊗` | 笛卡尔积有对角/投影；单oidal 张量一般**没有**到两因子的规范投影 |
| `fork` vs 元组值构造 | `fork` 是**任意对象上的配对态射**，不假设对象是集合 |
| 终对象 vs 单位类型「有用」 | 范畴终对象只保证唯一箭头；「能携带信息」是编程附加 |
| `one_unique` 写成 `f = g` | 本库是 `f ≈ g` |

## CoqIDE 步骤

1. 打开 `Structure/Terminal.v`，解释完 `Class Terminal`，再看 `terminal_unique` 的 `Program Definition`——观察 `Next Obligation` 如何只调用 `one_unique`。
2. 打开 `Structure/Cartesian.v`，停在 `ump_products`；用「左→右 / 右→左」各讲一遍。
3. 向下找到 `exl_fork` 或同类 corollary，看它如何从 UMP 推出来（典型证明：对 `ump_products` 取 → 方向）。
4. 打开 `Structure/Cocartesian.v`，对照注入/余配对命名，确认自己能说出对偶字典：`× ↔ +`、`fork ↔` 余配对、`exl/exr ↔ inl/inr`。
5. （可选）在 `Instance/Sets.v` 或 `Instance/Coq.v` 搜 `Terminal` / `Cartesian` 实例，看 `one`、`fork` 在具体范畴里填了什么。

## 相关笔记

积/和本身偏基础；与后续代数笔记的衔接见 [09](09-monad-algebra.md)、[11](11-lawvere-free.md)。总库：[haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

下一篇：[03 指数与笛卡尔闭](03-closed.md)
