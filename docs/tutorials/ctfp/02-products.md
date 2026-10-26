# 02 · 终/始对象、积与余积

**CTFP**：1.5 *Products and Coproducts*；1.6 *Simple Algebraic Data Types*。  
**DaoFP**：`4-SumTypes`、`5-ProductTypes`（并连带逻辑引入/消去、对偶、幺半直觉）。

> 教学复述，非书摘。

## 1. 书侧故事：用「普遍性质」代替「里面有什么」

CTFP 讲积/余积时，核心不是「积是有序对」这句话本身，而是：**给出投影行为之后，存在唯一的中介箭头**。程序员熟悉的 `(fst, snd)` / `Left|Right` 是 **Set** 上的模型；范畴论把「模型」换成「UMP（普遍映射性质）」，以便同一句话在别的范畴里仍有意义。

DaoFP 把和类型、积类型写成引入/消去规则，并点出与逻辑的对应（合取≈积、析取≈余积、真≈终、假≈始）。它还强调 **对偶**：把箭头反转，积的图变成余积的图——所以你学一套，得两套。

CTFP 1.6 进一步把 `Maybe`、列表等 ADT 看成用积/余积/1/0「搭积木」。本篇先把积木的 UMP 钉死；递归 ADT / 初始代数放到 [09](09-monad-algebra.md)、[11](11-lawvere-free.md) 与笔记 `docs/初始代数/`。

### 四个最小积木

| 概念 | 程序员直觉（Set） | UMP 一句话 |
|------|-------------------|------------|
| 终对象 `1` | `()` / `unit` | 到 `1` 的箭头唯一 |
| 初始对象 `0` | `Void` / `Empty` | 从 `0` 出发的箭头唯一 |
| 积 `x × y` | `(x, y)` | 一对投影；配对 `⟨f,g⟩` 唯一 |
| 余积 `x + y` | `Either x y` | 一对嵌入；`case` 唯一 |

## 2. 终对象与初始对象

### 本库：`Structure/Terminal.v`

```coq
Class Terminal := {
  terminal_obj : C;
  one {x} : x ~> terminal_obj;           (* ! : x ~> 1 *)
  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
}.
```

记号：对象侧 `1`，态射侧 `one` / `one[x]`。

**数据 vs 定律**：`one` 是「存在」；`one_unique` 是「唯一（在 ≈ 下）」。没有唯一性，只是「某个对象有进入射」，还不是终对象。

#### 证明走读 A：`one_comp`

```coq
Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.
```

| 步骤 | 说明 |
|------|------|
| Goal | `one ∘ f ≈ one`，类型都是 `x ~> 1` |
| `apply one_unique` | 任意两条进 `1` 的箭都 `≈`，无需知道 `f` 是什么 |
| 完成 | 这是 UMP 的力量：不展开具体范畴 |

CoqIDE：打开 `Terminal.v`，解释到该 Corollary，用「逐步」看 Proof 前后 Goal（若 IDE 支持把光标放进 Proof）。

#### 证明走读 B：`terminal_unique`（终对象在同构下唯一）

```coq
Program Definition terminal_unique {C : Category} (T1 T2 : @Terminal C) :
  @terminal_obj C T1 ≅ @terminal_obj C T2 := {|
  to   := @one C T2 (@terminal_obj C T1);
  from := @one C T1 (@terminal_obj C T2)
|}.
Next Obligation. apply (@one_unique C T2). Qed.
Next Obligation. apply (@one_unique C T1). Qed.
```

**在干什么**：`1₁ → 1₂` 取 T2 的 `one`；回来取 T1 的 `one`。互逆的 Goal 是 `to ∘ from ≈ id`——但两边都是「进到某个终对象」的箭，故 `one_unique` 一次性打掉。

CoqIDE 练习：

1. 解释 `Program Definition terminal_unique`。  
2. 打开 Obligations，看 `Next Obligation` 的 Goal 是否为 `≈ id`。  
3. 自己想：若不用 `one_unique`，能不能靠展开 `Sets` 证明？能，但那就不是「对任意范畴」的定理了。

`Initial.v` 对偶：字段常叫 `zero` / `zero_unique`（具体以文件为准）。把箭头倒过来读即可。

### 常值映射

```coq
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].
```

直觉：先把 `x` 唯一地丢进 `1`，再沿 `f` 选出 `y` 里的「点」。这正是 DaoFP / CTFP 说的「全局元 / 元素当箭头」。

## 3. 积：`Structure/Cartesian.v`

```coq
Class Cartesian := {
  product_obj : obj → obj → obj
    where "x × y" := (product_obj x y);

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z;  (* ⟨f,g⟩，记号常 △ *)

  exl {x y} : x × y ~> x;
  exr {x y} : x × y ~> y;

  fork_respects : ∀ x y z,
    Proper (equiv ==> equiv ==> equiv) (@fork x y z);

  ump_products {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> y × z) :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
}.
```

### UMP 怎么读成中文

对给定的 `f : x ~> y`、`g : x ~> z`：

- **存在**：`fork f g`（配对）满足 `exl ∘ ⟨f,g⟩ ≈ f` 且 `exr ∘ ⟨f,g⟩ ≈ g`；
- **唯一**：任何也满足这两条投影方程的 `h`，都有 `h ≈ ⟨f,g⟩`。

库把存在+唯一收成**一个双向** `ump_products`：左边是「`h` 就是配对」，右边是「投影还原 `f,g`」。

### 证明走读 C：从 UMP 取「投影—配对」

文件中有类似：

```coq
Corollary exl_fork {x z w : C} (f : x ~> z) (g : x ~> w) :
  exl ∘ (f △ g) ≈ f.
```

典型证明模式（精神；以源码为准）：

```coq
Proof.
  apply (proj1 (proj2 (ump_products f g (f △ g)) _)).
  (* 或 destruct (ump_products ...) 取方向 *)
Qed.
```

更可读的写法往往是：

```coq
Proof.
  apply ump_products.  (* 若陈述形式允许 *)
  (* 实际常见： *)
  pose proof (ump_products f g (f △ g)) as U.
  (* U : (f△g ≈ f△g) ↔ (exl∘(f△g)≈f)*(exr∘(f△g)≈g) *)
  (* 左边 refl，故得右边 *)
Qed.
```

CoqIDE 建议：

1. 搜索 `exl_fork`，逐步进入 Proof。  
2. 看中间 Goal 是否出现 `ump_products`。  
3. 再看 `fork_exl_exr`：`exl △ exr ≈ id`——「配对两个投影 = 积上的恒等」。

### 证明走读 D：`fork_comp`（配对与复合）

直觉：`⟨f,g⟩ ∘ h ≈ ⟨f∘h, g∘h⟩`。证明通常：

1. 要证两条箭 `≈`，用 UMP 的唯一性：证明它们跟投影复合后都等于同一对 `f∘h, g∘h`；  
2. 或用已证的 `exl_fork_comp` / `exr_fork_comp` 再拼。

这是「**不要展开积的具体实现，只打投影方程**」的标准范畴论证明风格；本库鼓励你这样做。

### 派生组合子

| 名字 | 约义 | 用途 |
|------|------|------|
| `first f` | `f × id` | 只改左分量 |
| `second f` | `id × f` | 只改右分量 |
| `split f g` | `f × g` | 两路并行 |
| `swap` | `exr △ exl` | 交换 |

看 `first_comp`、`swap_invol` 等定理时，Goal 仍是 `≈`；证明链仍是 UMP + `cat`。

`IsCartesianProduct`：不要求「全局的 `×`  bifunctor 式 API」，只说「这三个对象构成一组积结构」——读实例或证明「某对象是积」时用。

## 4. 余积：`Structure/Cocartesian.v`

对偶：

- `exl`/`exr` → 嵌入 `inl`/`inr`（名称以源码为准）；
- `fork`/`△` → `merge`/`case`/`▽`；
- UMP：给出 `f : y ~> x`、`g : z ~> x`，存在唯一 `y + z ~> x`。

程序员：`Either` 的 `either f g`。DaoFP §4 的 Bool / Maybe 枚举是余积积木的特例。

CoqIDE：打开 `Cocartesian.v`，对照 `Cartesian.v` 画一张「箭头反转」草图，标注哪张图对应 UMP。

## 5. 和 ADT 的关系（CTFP 1.6 视角，短述）

- `Maybe a` ≈ `1 + a`；
- 非空列表等可用积/余积嵌套表达形状；
- **递归**需要初始代数 / 不动点（本篇不展开），见笔记与 [11](11-lawvere-free.md)。

## 6. 易混对比

| 说法 | 澄清 |
|------|------|
| 「积就是 pair 类型」 | Set 上的模型；一般范畴只有 UMP |
| 有 `exl/exr` 就有积 | 还缺配对与唯一性（`ump_products`） |
| 终对象 = 初始对象 | 仅在零范畴等病态情况；Set 里 `()` ≠ `Void` |
| `fork_respects` 多余？ | setoid 范畴必需，否则 `≈` 不能传入配对 |
| 余积是「积的另一种写法」 | 对偶，不是语法糖 |

## 7. CoqIDE 检查清单

1. [ ] `Terminal`：解释 `one` / `one_unique`；跑通理解 `one_comp`。  
2. [ ] 逐步看完 `terminal_unique` 的两个 Obligation。  
3. [ ] `Cartesian`：解释 `ump_products` 双向各表示什么。  
4. [ ] 找到 `exl_fork`、`fork_exl_exr`，能复述证明思路（用 UMP，不展开）。  
5. [ ] 扫 `first`/`second`/`swap` 定义。  
6. [ ] `Cocartesian` 与积对照 5 分钟。  
7. [ ] （可选）`Instance/Sets` 或 `Instance/Coq` 里看积实例如何填字段。

## 和笔记的衔接

积/余积本身偏基础；进阶见笔记 [docs/幺半范畴/](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/%E5%B9%9A%E5%8D%8A%E8%8C%83%E7%95%B4)（单对象时的 monoid 对象）与 ADT/初始代数系列。

下一篇：[03 指数与笛卡尔闭](03-closed.md)
