# 01 · 范畴与态射

**CTFP**：Part One 中 *Category: The Essence of Composition*，以及 *Types and Functions* / *Categories Great and Small*（约 1.1–1.3）。  
**DaoFP**：`2-Composition`、`3-Isomorphism`。

## 这个概念在干什么

范畴论故意不问「对象里面有什么」。它只保留让**复合**有意义的最小结构：

- 一堆 **对象**；
- 对象之间的 **态射**（箭头）；
- 每个对象上的 **恒等**；
- 可结合的 **复合**。

性质一律用「进出这个对象的箭头」来说。Yoneda（见 [07](07-yoneda.md)）会告诉我们：这套纪律几乎不丢信息。

本库实现的是 **E-category**：`hom` 不是裸类型，而是带着等价关系 `≈` 的 setoid；复合必须尊重 `≈`。

## 短例子（直觉）

Haskell 里日常在用的「范畴」：

- 对象 ≈ 类型；
- 态射 ≈ 函数 `a -> b`；
- 恒等 ≈ `id`；
- 复合 ≈ `(.)`。

定律是：`id . f = f`、`f . id = f`、`(f . g) . h = f . (g . h)`。  
换到本库：把 `=` 换成 `≈`，并把「复合尊重相等」写成显式字段 `compose_respects`。

另一个常用例子：**关系范畴**（对象仍是集合，态射是关系，复合是关系合成）。同一套 `Category` 类装得下，说明「范畴」比「类型与函数」宽。

## 本库编码：`Class Category`

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

| 字段 | 含义 |
|------|------|
| `obj` | 对象的类型（宇宙 `o`） |
| `hom` / `~>` | 态射；记号在 morphism scope |
| `homset` | 每个 hom 是 Setoid → 相等是 `≈` |
| `id` / `compose` | 数据：恒等与复合（注意顺序：`f ∘ g` 先应用 `g`） |
| `compose_respects` | **setoid 义务**：`f≈f' → g≈g' → f∘g ≈ f'∘g'` |
| `id_left` / `id_right` | 单位律 |
| `comp_assoc` / `comp_assoc_sym` | 结合律及其对称写法 |

`comp_assoc_sym` 看起来冗余，但是刻意的：`Construction/Opposite.v` 构造对偶范畴时只需交换这两个字段，于是 **`C^op^op` 对 `C` 可由 reflexivity 收回**。实例作者若嫌烦，可用 `Build_Category'` 少填一个。

宇宙标注 `@{o h p}`：对象、hom、等价证明可以不在同一宇宙——读实例时偶尔会在 Goal 里看到，新手可先忽略，只要知道「这不是单宇宙玩具定义」。

### 典型 Goal 长什么样

证明 `id ∘ (f ∘ g) ≈ f ∘ g` 时，常见步骤是 `rewrite id_left` 或 `cat`（库里的范畴简化战术，见 `docs/AUTOMATION`）。  
若 Goal 是 `f ∘ g ≈ f' ∘ g'`，你往往先用 `compose_respects` / `proper`，再分别攻 `f≈f'` 与 `g≈g'`。

## 同构：`Theory/Isomorphism.v`

同构不是「看起来像」，而是一对互逆态射：

```coq
Class Isomorphism (x y : C) : Type := {
  to   : x ~> y;
  from : y ~> x;
  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.
```

记号常写作 `x ≅ y`。注意：相等仍是 `≈`。  
终对象「在同构下唯一」、伴随「右伴随在自然同构下唯一」等定理，底层都靠这个类。

## 态射性质：`Theory/Morphisms.v`

单射/满射的范畴版：

- **mono**（左消）：`f ∘ g ≈ f ∘ h → g ≈ h`；
- **epi**（右消）：对偶。

编程直觉：在 **Set** 里 mono≈单射、epi≈满射；在别的范畴不必成立字面集合论含义，但消除律的形状一样。读极限/伴随保持性时会用到。

## 对偶：`Construction/Opposite.v`

`C^op`：对象不变，箭头反向，复合顺序对调。本库通过对换 `comp_assoc` / `comp_assoc_sym` 让对偶干净。  
**用法**：许多「余××」定义成「对偶范畴里的 ××」——例如余极限 ≈ 对偶里的极限（见 [06](06-limits.md)）。看到 `F^op`、`C^op` 不要慌，先画反箭头。

## 程序侧入口：`Theory/Coq.v`

这不是「Coq 证明助手本身是范畴」的完整故事，而是一组面向编程的子库入口（`Theory/Coq/Functor.v`、`Monad.v` 等），把 fmap / bind 习惯接到 Gallina。细节放到 [12](12-instances.md)；此处只需知道：**同一套抽象，Instance/Coq 与 Theory/Coq 两条落地线**。

## 易混对比

| 说法 | 澄清 |
|------|------|
| 「对象等于类型」 | 只是 **Set/Coq 实例** 的直觉；一般范畴对象可以是群、空间、别的范畴… |
| `=` vs `≈` | 本库态射相等几乎总是 `≈`；`=` 多用于对象级定义等式或结构相等 |
| 「有对象就有元素」 | 范畴不论域；「元素」常编码为 `1 ~> X`（全局元），见终对象篇 |
| 同构 vs 相等 | 范畴论偏爱 `≅`；不要强行改成对象 `=` |

## CoqIDE 步骤

1. 打开 `Theory/Category.v`，滚动到 `Class Category`（跳过文首历史长注释）。
2. 逐步解释整个 `Class` 体；在 `homset`、`compose_respects` 停一下，确认 `Existing Instance` 已导出。
3. 在 Proof General / VsCoq 里任意搜一个用到 `id_left` 的 lemma，看 `≈` Goal。
4. 打开 `Theory/Isomorphism.v`，找到 `Class Isomorphism` 与 `≅` 记号。
5. 打开 `Construction/Opposite.v`，看 `op` 如何定义 `compose`，以及 `comp_assoc` 字段如何对调。
6. （可选）扫 `Theory/Morphisms.v` 里 mono/epi 定义各 1 分钟。

## 和笔记的衔接

范畴本身在笔记里通常不单开长文；从 [02](02-products.md) 开始会链到 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 的具体主题。

下一篇：[02 积、和与终始对象](02-products.md)
