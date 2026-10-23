# 03 · 指数对象与笛卡尔闭

**CTFP**：1.9 *Function Types*。  
**DaoFP**：`6-FunctionTypes`（引入/消去、柯里化、与 λ / 逻辑的对照；积与和的再访；函数类型的函子性）。

> 下文为原创教学复述，只引章节标题；不摘录书中正文。

## 1. 书侧故事：函数类型为什么要「变成对象」

前面几课里，两个对象之间的箭头活在 **hom-setoid** 里。对程序员来说，`A -> B` 本身又是一个类型——可以当参数、当返回值、可以放进容器。CTFP 1.9 与 DaoFP §6 要解决的，正是把这种「箭头再当对象」的需求写成范畴论：

> 若范畴有积，何时存在对象 `B^A`，使得从 `C × A` 到 `B` 的箭头，与从 `C` 到 `B^A` 的箭头，自然一一对应？

这个对象叫 **指数**（或内齐 Hom）。有限积 + 全体指数存在 = **笛卡尔闭范畴（CCC）**。Set 与「理想化 Hask」是 CCC；许多语义范畴也是。

DaoFP 用类型论口吻对齐：

- **引入**（抽象）：造出指向指数的箭头，对应 λ；  
- **消去**（应用）：`eval : B^A × A ~> B`，对应函数应用 / modus ponens；  
- **β**：先引入再消去 ≈ 原箭头——本库 `ump_exponents`；  
- **η / 外延精神**：指数上的箭头由其「应用行为」决定——体现在 `curry_uncurry` 等。

CTFP 则更多从程序员柯里化经验讲起：`((A,B) -> C) ≅ (A -> (B -> C))`，再抽象成 UMP。两条叙事同一终点。

### 和「外部 Hom」的差别

只有 `hom(A,B) : Type` 并不自动给出范畴**内**的对象 `B^A`。CCC 要求指数是 `obj` 里的东西，且与积形成伴随（见 [08](08-adjunction.md)）。读本库时：看到 `Closed` 的 `exponent_obj`，才是内齐；看到 `Sets` 里的 `homset`，只是外部相等结构。

## 2. 编程直觉（短）

```haskell
curry   :: ((x, y) -> z) -> x -> y -> z
uncurry :: (x -> y -> z) -> (x, y) -> z
eval    :: (y -> z, y) -> z          -- ~ uncurry id
-- β 精神: eval . bimap (curry f) id  ≃  f
```

在 Set：`z^y` 就是函数集合。在别的 CCC，指数对象可能是「连续函数空间」「可计算函数」等——UMP 形状不变。

函数类型的函子性（DaoFP 亦提）：`B^A` 对 `B` 协变、对 `A` 反变。本库后续 `fmap` 进指数时要注意方差；初学先盯住 `curry`/`eval`。

## 3. 本库：`Structure/Cartesian/Closed.v`

前置：已有 `Cartesian`（[02](02-products.md)）。

```coq
Class Closed := {
  exponent_obj : obj → obj → obj
    where "y ^ x" := (exponent_obj x y);

  exp_iso {x y z} : x × y ~> z ≊ x ~> z^y;

  curry'   {x y z} := to (@exp_iso x y z);
  uncurry' {x y z} := from (@exp_iso x y z);

  eval' {x y} : y^x × x ~> y := uncurry' id;

  ump_exponents' {x y z} (f : x × y ~> z) :
    eval' ∘ first (curry' f) ≈ f
}.
```

导出名：`curry` / `uncurry` / `eval` / `ump_exponents`。  
**记号**：`y ^ x` 在本库等于 `exponent_obj x y`——读实例时核对参数顺序，勿与 `Hom(x,y)` 的书写习惯混用。

| 字段 | 角色 |
|------|------|
| `exponent_obj` | 指数对象 |
| `exp_iso` | 柯里化的 setoid 同构（在 `Sets` 意义下的 `≊`） |
| `curry'` / `uncurry'` | 同构两向 |
| `eval'` | counit，求值 |
| `ump_exponents'` | β：`eval ∘ (curry f × id) ≈ f` |

唯一性多半来自同构本身（见 `uncurry_curry`），不必再单独写一条 `unique`。

`Structure/BiCCC.v`：在笛卡尔闭基础上再打包余积等，成为双笛卡尔闭；按需打开。

## 4. CoqIDE 证明走读

### 4.1 定位与解释

1. 打开 `Structure/Cartesian/Closed.v`。  
2. 确认上下文已 `Require` 积结构。  
3. 逐步解释整个 `Class Closed`。  
4. 看 `Notation "y ^ x"` 与 `Definition curry` 包装。

### 4.2 β 方程：`ump_exponents`

Goal 类型：`eval ∘ first (curry f) ≈ f`。  
读图：

```text
x × y  --first(curry f)-->  (z^y) × y  --eval-->  z
         （先把左边变成「柯里化后的函数」再应用）
```

不要想成「展开 λ 项」；想成伴随 counit。CoqIDE：搜索 `ump_exponents`，看它是否只是 `ump_exponents'` 的别名。

### 4.3 同构两向：`curry_uncurry` / `uncurry_curry`

```coq
Corollary curry_uncurry {x y z} (f : x ~> z^y) :
  curry (uncurry f) ≈ f.
Corollary uncurry_curry {x y z} (f : x × y ~> z) :
  uncurry (curry f) ≈ f.
```

**典型证明步骤**：

1. `unfold curry, uncurry`（或 `simpl`）变成 `to/from exp_iso`；  
2. `rewrite iso_to_from` 或 `iso_from_to`；  
3. 必要时 `destruct exp_iso`；末尾 `cat` / `reflexivity`。

Obligation 若出现 `Proper`，用 `proper`。

### 4.4 `curry_inj`：由同构单性推原箭头单

```coq
Corollary curry_inj {x y z} (f g : x × y ~> z) :
  curry f ≈ curry g → f ≈ g.
```

思路：假设 `curry f ≈ curry g`，两边作用 `uncurry`（或两边接 `eval ∘ first (−)`），用 β / `uncurry_curry` 还原。  
**练习**：在 Scratch 里对抽象 `Closed` 重写一版（可抄源码结构），强迫自己点 `rewrite`。

### 4.5 `eval_curry` / `curry_comp`

这些 Corollary 描述「应用与复合」如何通过柯里化搬运。证明链通常：

`ump_exponents` + `first_fork`/`exl_fork` 等积引理 + `compose_respects` + `cat`。

读时在纸上画积的图，标出 `first` 改左分量——与 [02](02-products.md) 的 `first` 定义对照。

### 4.6 和伴随的接口

积函子 `(− × y) ⊣ (−)^y` 的 Hom 同构正是 `exp_iso`。若库中有该 `Adjunction` 实例，打开后应能看到 `⌊⌋` 即 `curry`。详见 [08](08-adjunction.md)。

## 5. 易混对比

| 说法 | 澄清 |
|------|------|
| 有 `A -> B` 类型就有 CCC | 那是外部语言；范畴内要有 `exponent_obj` + UMP |
| `Closed` 只要 `curry` 函数 | 本库要同构 + β |
| 记号 `y^x` | 核对参数序 |
| 闭幺半范畴 | ⊗ 版内齐 Hom；积是特例；见 [10](10-monoidal-kan-ends.md) |
| `BiCCC` | 同时要余积等；不是「两个 CCC」 |

## 6. CoqIDE 检查清单

1. [ ] 解释 `Closed` 全字段；默写 `eval` 定义。  
2. [ ] 追 `ump_exponents` 的类型与图。  
3. [ ] 跟完 `curry_uncurry` / `uncurry_curry`。  
4. [ ] 读 `curry_inj` 或自证精神版。  
5. [ ] 扫 `flip`、`curry_comp`、`eval_first`。  
6. [ ] 打开 `BiCCC.v` 看打包假设。  
7. [ ] （可选）在 Sets 实例里指认指数对象。

## 和笔记 / 后文

指数为伴随与 Monad（State 等）铺路。笔记 Lawvere / 笛卡尔闭语义若出现「内齐语言」，回看本篇 UMP。



## 10. Scratch 迷你题（抽象 Closed）

在已 `Require` 积与 `Closed` 的上下文：

```coq
Example beta_like `{Closed C} {x y z} (f : x × y ~> z) :
  eval ∘ first (curry f) ≈ f.
Proof. apply ump_exponents. Qed.
```

再试证 `curry (eval) ≈ id` 的精神版（若库有 `curry_eval` 则 `apply` 之；否则展开定义）。把成功的 Proof 留在本地笔记，勿提交密钥或无关文件。


下一篇：[04 函子](04-functor.md)
