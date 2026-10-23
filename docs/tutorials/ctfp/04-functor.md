# 04 · 函子

**CTFP**：约 1.7–1.8（函子相关章）。  
**DaoFP**：`8-Functoriality` 一带。  
**笔记**：[haskell-algebra-notes · 函子组合](https://github.com/exsabersac/haskell-algebra-notes)。

## 这个概念在干什么

函子是**范畴之间的同态**：把对象送到对象、态射送到态射，并**保住恒等与复合**。

两句并行的话：

1. **向外**：把一整套结构从世界 A 搬到世界 B（同调、遗忘、自由、嵌入…）；
2. **向内**：进入 `C` 的函子 `J ⟶ C` 就是 `C` 里形状为 `J` 的图——极限理论吃的就是这种图（见 [06](06-limits.md)）。

范畴论历史上，函子与自然变换才是主角；范畴是为了让它们有定义域/陪域才引入的（Eilenberg–Mac Lane）。

## 短例子

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
-- 定律：
-- fmap id = id
-- fmap (g . f) = fmap g . fmap f
```

`Maybe`、`[]`、`(->) r` 都是自函子（在 Hask ≈ 类型范畴上）。  
本库的差别：**还有第三条**——`fmap` 必须尊重态射的 `≈`（`fmap_respects`）。Haskell 里常被 parametricity「藏起来」；在一般 E-category 上必须手写。

## 本库：`Theory/Functor.v`

```coq
Class Functor {C : Category} {D : Category} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects : ∀ x y,
    Proper (equiv ==> equiv) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
```

记号：函子常写作 `F : C ⟶ D`（粗箭头）；对象作用可写 `F x`（经 coercion / 记号），态射作用 `fmap[F] f`。

### 三条定律分别防什么

| 定律 | 若破坏会怎样 |
|------|----------------|
| `fmap_id` | 「结构映射」连恒等都不保，复合语义崩 |
| `fmap_comp` | 不能把复合搬进映像——图的交换性全坏 |
| `fmap_respects` | 无法在 setoid 上重写；`f≈g` 推不出 `fmap f ≈ fmap g` |

### 函子相等是什么

本库默认函子的 setoid（`Functor_Setoid`）不是「对象映射点点 `=`」，而更接近**自然同构意义下的相等**（读文件后部）。因此 `Id`、复合 `◯` 组成的「范畴的范畴」在 `Instance/Cat.v` 里能工作，但相等要按库定义理解——这是读 Cat 实例时的常见卡点。

更严的 `Functor_StrictEq_Setoid` 也在同文件末尾，需要时再切换。

## 编程子库：`Theory/Coq/Functor.v`

面向 Gallina/程序员习惯的仅 fmap 类；定律按实例消解。与 `Theory/Functor.v` 抽象层次不同：**学范畴定义读 Theory；写 Coq 程序感读 Theory/Coq**。`Functor/Applicative.v` 是后续加厚缺口之一。

## 「种」与保结构：`Functor/Structure/`

若源范畴有终对象/积/幺半等，目标也有，你可以要求函子**保**这些结构，例如：

- `Functor/Structure/Terminal.v` → `TerminalFunctor`
- `Functor/Structure/Cartesian.v` → `CartesianFunctor`
- `Functor/Structure/Monoidal.v` → `MonoidalFunctor`

Lawvere 模型「保有限积的函子」就是这一纪律的代数版（见 [11](11-lawvere-free.md)）。

## 易混对比

| 易混 | 分清 |
|------|------|
| 自函子 `C ⟶ C` vs 一般函子 | Monad/代数吃自函子；极限形状图常是 `J ⟶ C` |
| `fmap` 方向 | 共变：`x~>y` 变成 `Fx~>Fy`；反变要经 `C^op` 或单独记 |
| 函子 vs 函数 | 函子动整层范畴；函数是某个范畴里的一条态射 |
| Haskell 第二定律「可推导」 | 在任意 setoid 范畴上 **`fmap_comp` 不可省** |

## CoqIDE 步骤

1. 打开 `Theory/Functor.v`，解释完 `Class Functor` 三个定律字段。
2. 找到函子复合与 `Id` 的定义（同文件后部），看 `fun_equiv_id_left` 一类引理的陈述——感受「差一个自然同构」。
3. 打开 `Theory/Coq/Functor.v`，对比字段多少。
4. 打开 `Functor/Structure/Cartesian.v` 瞄一眼「保积」要多交哪些证明。
5. （可选）`Instance/Fun.v`：函子范畴 `[C,D]` 的对象是函子、态射是自然变换——为 [05](05-natural.md) 铺路。

## 相关笔记

函子水平复合、Day 卷积等见笔记「函子组合」目录：[haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。


## 在库里「当函子用」时实际发生什么

声明 `{F : C ⟶ D}` 后，你通常会写 `fmap[F] f`。若 `F` 来自 typeclass 推断失败，显式传入：

```coq
fmap (F:=MyFunctor) f
(* 或 *)
fmap[MyFunctor] f
```

复合记号在库中常见为 `G ◯ F`（先 `F` 后 `G`，与 `∘` 同序习惯一致——读定义确认）。  
恒等函子 `Id`：`fobj` 是恒等、`fmap` 是恒等态射；定律义务几乎是 `reflexivity` / `cat`。

### 反变怎么处理

本库偏好：**不另建 Contravariant 类**，而是写 `C^op ⟶ D` 或 `C ⟶ D^op`。  
Yoneda 预层是 `C^op ⟶ Sets`；读 `fmap` 时记住 `C^op` 的态射已经反向。  
若你从 Haskell `Contravariant` 过来，先画一次 `op`，再对字段。

### 证明 `fmap_comp` 的常见形状

Goal：

```text
fmap (f ∘ g) ≈ fmap f ∘ fmap g
```

若 `fmap` 定义为「对底层函数加工」：

1. 展开 `fmap`；
2. 用底层范畴的 `comp_assoc` / 函数复合定义；
3. `proper` 处理 `≈`；
4. 收尾 `reflexivity` 或 `cat`。

Sets 实例里这往往化成点点相等；抽象范畴里则依赖你对 `fobj` 的构造方式。

下一篇：[05 自然变换](05-natural.md)
