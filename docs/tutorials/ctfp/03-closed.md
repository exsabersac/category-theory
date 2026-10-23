# 03 · 指数对象与笛卡尔闭范畴（CCC）

**CTFP**：约 1.9（函数类型 / 指数相关章）。  
**DaoFP**：`6-FunctionTypes` 一带。

## 这个概念在干什么

积让你「同时拥有」两个对象；**指数**（内部 hom）让你把「从 `y` 到 `z` 的箭头」**重新变成对象** `z^y`，从而支持柯里化：

```text
(x × y ~> z)  ≃  (x ~> z^y)
```

带有限积且每个指数都存在的范畴叫 **笛卡尔闭范畴（CCC）**。编程语言里：函数类型 `y -> z`、λ/应用、柯里化，正是 CCC 的日常脸。

## 短例子

```haskell
curry   :: ((x, y) -> z) -> (x -> (y -> z))
uncurry :: (x -> (y -> z)) -> ((x, y) -> z)
eval    :: (y -> z, y) -> z
-- eval (f, a) = f a
```

UMP 直觉：`eval ∘ (curry f × id) = f`——先柯里化再应用，回到原来的二元函数。

## 本库路径：先分清两个文件

| 文件 | 状态 | 你该怎么用 |
|------|------|------------|
| `Structure/Cartesian/Closed.v` | **完整可用的 CCC 指数** | 主读这个 |
| `Structure/Closed.v` | Eilenberg–Kelly「闭范畴」**草稿**（`Closed` 类被注释掉） | 只看 `Curry`/`Flip` 助手；不要当成 CCC |
| `Structure/Monoidal/Closed.v` | 闭**幺半**（张量-hom） | 有 `⊗` 时再读；与笛卡尔指数不同 |
| `Structure/BiCCC.v` | 双笛卡尔闭（兼余积） | 有和+函数类型时 |

新手主线：**`Cartesian` + `Cartesian/Closed`**。

## 核心类：`Structure/Cartesian/Closed.v`

前置：`Context `{@Cartesian C}``——没有积就谈不上这个指数定义。

```coq
Class Closed := {
  exponent_obj : obj → obj → obj
    where "y ^ x" := (exponent_obj x y);

  exp_iso {x y z} : x × y ~> z ≊ x ~> z^y;

  curry'   {x y z} : x × y ~> z → x ~> z^y := to   (@exp_iso x y z);
  uncurry' {x y z} : x ~> z^y → x × y ~> z := from (@exp_iso x y z);

  eval' {x y} : y^x × x ~> y := @uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x × y ~> z) :
    eval' ∘ first (@curry' _ _ _ f) ≈ f
}.
```

### 字段怎么读

| 名字 | 含义 |
|------|------|
| `y ^ x` | 指数对象（注意参数序：`exponent_obj x y` 显示成 `y^x`） |
| `exp_iso` | 柯里化在 **Sets 意义下的同构**（`≊`），两边是 setoid 的 hom |
| `curry` / `uncurry` | 同构的两个方向 |
| `eval` | 余单位形状：`uncurry id`，即应用态射 `(y^x) × x ~> y` |
| `ump_exponents` | β/计算规则：`eval ∘ first (curry f) ≈ f` |

`first (curry f)` 即 `curry f × id`：只改积的左臂。

文件后文还有 `curry_uncurry`、`uncurry_curry` 等，说明 `exp_iso` 真是同构——唯一性往往藏在「同构」里，而不另写一条冗长 UMP。

### 典型 Goal

证某态射等于 `curry f` 时，常见策略：

1. 两边 `uncurry`，变成积上的等式；
2. 或利用 `ump_exponents` 把目标改成与 `eval` 的交互；
3. 需要 `Proper` 时用 `curry_respects` / `uncurry_respects`。

## 和伴随的关系（预告）

指数的本质是伴随：

```text
(− × y)  ⊣  (−)^y
```

左伴随是「固定 `y` 的积函子」，右伴随是「指数 `−^y`」。单位/余单位对应柯里化与 `eval`。  
正式展开见 [08](08-adjunction.md) 与 `Adjunction/Diagonal/Product.v` 一类文件；本篇先会用 `Closed` 字段即可。

## 易混对比

| 易混 | 分清 |
|------|------|
| `Structure/Closed.v` vs `Cartesian/Closed.v` | 前者是通用闭范畴草稿；**CCC 用后者** |
| 笛卡尔闭 vs 幺半闭 | 一个用 `×`，一个用 `⊗`；有投影的是笛卡尔 |
| `y^x` 参数顺序 | 显示是 `y^x`，构造子是 `exponent_obj x y`——看定义别看感觉 |
| 「有函数类型就有 λ」 | CCC 给指数与 eval/curry；完整 λ 演算模型还要更多（见 `Instance/Lambda/`） |

## CoqIDE 步骤

1. 确认已能解释 `Structure/Cartesian.v` 的 `first`。
2. 打开 `Structure/Cartesian/Closed.v`，解释 `Class Closed` 到 `ump_exponents'`。
3. 看 `eval` 的定义等于 `uncurry id`——用一句话解释为何这是「应用」。
4. 执行/阅读 `curry_uncurry`、`uncurry_curry` 的 proof，观察它们如何调用 `iso_to_from` / `iso_from_to`。
5. 打开 `Structure/Closed.v` 顶部注释，确认 `Closed` 类被关掉；浏览 `Curry`/`Flip` 即可离开。
6. （可选）`Structure/BiCCC.v` 看如何把笛卡尔 + 余笛卡尔 + 闭打成一包。

## 相关笔记

函数类型与伴随的编程展开，可对照笔记总库 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)；Lawvere/CCC 更深的语义放到 [11](11-lawvere-free.md)。

下一篇：[04 函子](04-functor.md)
