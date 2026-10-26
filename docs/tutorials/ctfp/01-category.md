# 01 · 范畴与态射

**CTFP**：1.1 *Category: The Essence of Composition*；1.2 *Types and Functions*；1.3 *Categories Great and Small*。  
**DaoFP**：`1-CleanSlate`、`2-Composition`、`3-Isomorphism`。

> 下文是教学复述，不是书摘。原书请读上述章节。

## 1. 书侧故事：为什么要从「复合」讲起

CTFP 开篇把范畴论的核心压成一句话：**可结合的复合，外加对每个对象无作用的恒等**。程序员每天都在写 `h . g . f`（或管道 `|>`）；范畴论把这种「串起来」提成数学对象，并规定：只有声明了复合与恒等、且满足单位律与结合律，才叫范畴。

DaoFP 的切入更「类型论」：先清掉「集合里有元素」的默认画面（Clean Slate），再谈类型与函数、箭头对象、yin-yang 式的对偶。它强调：**元素常常可以编码成从终对象出发的箭头**（后面终对象篇会落地），所以「只谈箭头」并不是故弄玄虚。

两本书都会尽快给你程序员最熟的例子：

- **对象** ≈ 类型；
- **态射** ≈ 函数 `A -> B`；
- **恒等** ≈ `id`；
- **复合** ≈ `(.)`。

然后立刻警告：这只是 **Set / Hask 直觉**。还有「对象是别的范畴」「态射是关系 / 证明 / 函子」等实例（CTFP 1.3 *Categories Great and Small* 扫了一圈小范畴、预序、幺半群当单对象范畴等）。本库用同一套 `Class Category` 装下它们。

### 你应该带走的三点动机

1. **不打开对象看内部**：性质用进出箭头刻画（为 Yoneda 铺路）。
2. **复合是一等公民**：比「元素上的运算」更适合谈程序结构。
3. **同构优于相等**：能可逆来回就够用，不必强迫对象字面相等。

## 2. 编程直觉（短例子）

```haskell
-- 单位律与结合律（Haskell 风格；= 在真 Hask 里要小心底序）
id . f = f
f . id = f
(f . g) . h = f . (g . h)
```

另一个本库也在意的例子：**关系范畴**——对象仍是集合，态射是关系，复合是关系合成。同一 `Category` 类装得下，说明抽象比「类型与函数」宽。

预序：对象是元素，`a ~> b` 至多一条（有序证明），复合是传递。幺半群：单对象范畴，态射是幺半群元素，复合是乘法——CTFP / DaoFP 都会用这个例子说明「范畴可以很小」。

## 3. 本库编码：`Class Category`

文件：`Theory/Category.v`。

```coq
Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};
  hom : obj → obj → uhom where "a ~> b" := (hom a b);
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);

  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);

  compose_respects {x y z} :
    Proper (equiv ==> equiv ==> equiv) (@compose x y z);

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;
  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.
```

### 字段怎么读

| 字段 | 含义 | 证明里怎么用 |
|------|------|--------------|
| `obj` | 对象的类型（宇宙 `o`） | 很少直接改；实例里给出具体 `Type` |
| `hom` / `~>` | 态射 | Goal 的类型常常是 `x ~> y` |
| `homset` | 每个 hom 是 Setoid → 相等是 `≈` | 导出 `Equivalence`，才能 `rewrite`/`reflexivity` |
| `id` / `compose` | 数据；`f ∘ g` **先**应用 `g` | 与 Haskell `(f . g) x = f (g x)` 同序 |
| `compose_respects` | setoid 义务 | `f≈f' → g≈g' → f∘g ≈ f'∘g'`；`proper` 战术常消此类 Goal |
| `id_left` / `id_right` | 单位律 | `rewrite id_left` 是最常见一步 |
| `comp_assoc` / `comp_assoc_sym` | 结合律双向 | 为对偶范畴准备；见下 |

`comp_assoc_sym` 看起来冗余，但是刻意的：`Construction/Opposite.v` 构造 `C^op` 时只需交换这两个字段，于是 **`C^op^op` 对 `C` 可由 reflexivity 收回**。实例作者若嫌烦，可用 `Build_Category'` 少填一个。

宇宙 `@{o h p}`：对象、hom、等价证明可不在同一宇宙。新手可先忽略，只要知道「不是单宇宙玩具定义」。

## 4. CoqIDE 证明走读

### 4.1 打开与定位

1. CoqIDE / VsCoq 打开仓库根（认 `_CoqProject`）。
2. 打开 `Theory/Category.v`，**跳过**文首长注释，搜索 `Class Category`。
3. 把光标放在 `Class` 的 `.` 之后，逐步解释（CoqIDE：向下箭头 / `Alt+↓`），直到整个类体被消化。
4. 确认 `Existing Instance` 之类导出已执行——后面才能搜到 `id_left` 作 rewrite 提示。

### 4.2 手证一条「像书上单位律」的 Goal

在 *Scratch* 缓冲或临时 `Section` 里（需已 `Require Import Category.Theory.Category`）：

```coq
Section Walkthrough.
  Context {C : Category} {x y z : C} (f : y ~> z) (g : x ~> y).

  Example id_after_comp : id ∘ (f ∘ g) ≈ f ∘ g.
  Proof.
    (* Goal: id ∘ (f ∘ g) ≈ f ∘ g *)
    rewrite id_left.
    (* Goal: f ∘ g ≈ f ∘ g *)
    reflexivity.
  Qed.

  Example assoc_once :
    f ∘ (g ∘ id) ≈ (f ∘ g) ∘ id.
  Proof.
    rewrite id_right.           (* 内层 g ∘ id ≈ g，需 setoid 在 ∘ 下 Proper *)
    rewrite id_right.
    reflexivity.
  Qed.
End Walkthrough.
```

**逐步心理活动**：

| 步骤 | Goal 变化 | 用到的概念 |
|------|-----------|------------|
| 开始 | `id ∘ (f ∘ g) ≈ f ∘ g` | 要证的等式 |
| `rewrite id_left` | `f ∘ g ≈ f ∘ g` | 字段 `id_left`；左边 `id ∘ _` 被吃掉 |
| `reflexivity` | 完成 | `homset` 给的 `Equivalence` |

若 `rewrite id_right` 报错「不能 rewrite」，多半是 **Proper 实例没在作用域**：确认 `compose_respects` 已 `Existing Instance`，或先 `Setoid`/`Proper` 相关导入。本库正常 `Require Import Category.Theory.` 后应可用。

### 4.3 用库战术收尾

把上面证明改成：

```coq
Proof. cat. Qed.
```

`cat`（见 `docs/AUTOMATION.md`）会做 simplify + `autorewrite with categories` + `auto with category_laws`。教学阶段建议**先手写字段 rewrite**，确认自己认得定律，再让 `cat` 当抄写员。

### 4.4 `compose_respects` 长什么样

当你证明 `f ∘ g ≈ f' ∘ g'` 且已知 `f≈f'`、`g≈g'`：

```coq
apply compose_respects; assumption.
(* 或 *)
rewrite H_f, H_g; reflexivity.
```

Goal 若直接是 `Proper (equiv ==> equiv ==> equiv) (@compose x y z)`，试 `proper` 或 `apply compose_respects`。

## 5. 同构：`Theory/Isomorphism.v`

DaoFP §3 与 CTFP 多处强调：范畴论爱 **同构** 不爱「对象相等」。本库：

```coq
Class Isomorphism (x y : C) : Type := {
  to   : x ~> y;
  from : y ~> x;
  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.
```

记号常 `x ≅ y`。注意互逆等式仍是 `≈`。

**走读**：打开 `Isomorphism.v`，找到 `Class Isomorphism`，再找一个 `Program Definition` 造同构的例子（例如终对象唯一性会用到，见 [02](02-products.md)）。`Next Obligation` 里典型 Goal 就是 `to ∘ from ≈ id`——此时往往 `apply one_unique` 或具体范畴的计算。

## 6. 态射性质：`Theory/Morphisms.v`

- **mono**（左消）：`f ∘ g ≈ f ∘ h → g ≈ h`；
- **epi**（右消）：对偶。

在 **Set** 里 mono≈单射、epi≈满射；一般范畴只保留消除律形状。读极限保持、伴随忠实/全时时会用到。

CoqIDE：搜索 `Monomorphism` / `mono`，看定义是 `Prop`/`Type` 包装还是直接字段；尝试理解「消元」如何写成对任意 `g h` 的蕴含。

## 7. 对偶：`Construction/Opposite.v`

`C^op`：对象不变，箭头反向，复合顺序对调。本库通过对换 `comp_assoc` / `comp_assoc_sym` 让对偶干净。

**走读步骤**：

1. 打开 `Opposite.v`，找到给 `C^op` 填的 `Category` 实例。
2. 看 `compose` 如何用原来的 `compose` 对调参数。
3. 看 `comp_assoc` 字段填的是原范畴的哪一个。
4. 搜索 `op_op` 或双重对偶相关 lemma，确认「对偶两次回来」是定义上的 refl，不是大定理。

用法：许多「余××」=「对偶里的 ××」。见 [06](06-limits.md)。

## 8. 程序侧入口：`Theory/Coq.v`

面向编程的子库入口（`Theory/Coq/Functor.v`、`Monad.v` 等）。细节在 [12](12-instances.md)。此处只需知：同一套抽象，**Instance/Coq** 与 **Theory/Coq** 两条落地线。

## 9. 易混对比

| 说法 | 澄清 |
|------|------|
| 「对象等于类型」 | 只是 Set/Coq 实例直觉；一般对象可以是群、空间、范畴… |
| `=` vs `≈` | 态射层几乎总是 `≈`；`=` 多用于对象级定义或结构相等 |
| 「有对象就有元素」 | 范畴不论域；元素常编码为 `1 ~> X` |
| 同构 vs 相等 | 偏爱 `≅`；不要强行改成对象 `=` |
| Hask 里的 `=` | 底序、partiality 让「真范畴」有争议；本库用 setoid 更诚实 |

## 10. CoqIDE 检查清单

1. [ ] `Class Category` 整表解释通过，无红叉。  
2. [ ] 手写 `rewrite id_left` 例子成功。  
3. [ ] 同一例子改 `cat` 也能过。  
4. [ ] 打开 `Isomorphism.v`，看懂四个字段。  
5. [ ] 打开 `Opposite.v`，指出复合如何反向。  
6. [ ] （可选）`Morphisms.v` 里 mono 定义读 2 分钟。

## 和笔记的衔接

范畴总论在笔记里通常不单开长文；从 [02](02-products.md) 起链到 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

下一篇：[02 积、和与终始对象](02-products.md)
