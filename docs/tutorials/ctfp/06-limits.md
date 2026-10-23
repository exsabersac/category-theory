# 06 · 锥与（余）极限

**CTFP**：约 Part Two 的极限章（2.2 一带）。  
**DaoFP**：自然变换章后的 Limits 节。

## 这个概念在干什么

积、终对象、等化子、拉回……外形不同，共用一句：

> 对某个形状的图，存在一个**万有锥**（极限）：任意其他锥都经唯一中介箭头因子分解。

余极限是对偶（万有余锥）。学极限是为了**一张表统一 UMP**，而不是背更多名词。

## 机制：图 → 锥 → 极限

1. **图 / 形状**：函子 `F : J ⟶ C`。`J` 的对象是「角点」，态射是「要交换的边」；`F` 把形状画进 `C`。
2. **锥** `Cone F`：一个顶点（apex）`vertex_obj`，加上到各 `F j` 的腿，使所有边交换（`cone_coherence`）。
3. **极限**：一个特殊锥 `limit_cone`，满足 UMP——任何锥 `N` 都有唯一 `u : N ~> limit_cone`，与所有腿相容。

空图 → 终对象；两点无边 → 积；平行双箭头 → 等化子；拉回形状 → pullback。

## 短例子

积作为极限：

```text
        a
       / \
     f/   \g
     v     v
     x     y
```

万有顶点是 `x×y`，腿是 `exl`、`exr`；任意 `a` 上的 `(f,g)` 唯一写成经 `fork` 的因子。

Haskell 里很少直接写 `Limit`，但 `unzip`、拉回式约束、数据库 join 的「万有」味道都是亲戚。

## 本库编码

### `Structure/Cone.v`

```coq
Class Cone {J C} (F : J ⟶ C) := {
  vertex_obj : C;
  coneFrom : ACone vertex_obj F
}.
```

`ACone` 携带腿族 `vertex_map` 与交换条件。  
`Cocone F := Cone (F^op)`——余锥直接对偶定义。

还有 `ConePresheaf`：把「以 `c` 为顶的锥」做成反变函子，后面用极限的可表性/伴随观点时会碰到。

### `Structure/Limit.v`

```coq
Class Limit (F : J ⟶ C) := {
  limit_cone : Cone F;
  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x : J,
    vertex_map[limit_cone] ∘ u ≈ vertex_map[N] x
}.
```

`∃!`：存在唯一中介态射（在库的 `Unique` 意义下）。  
`IsALimit`：谓词版「对象 `c` 是该图的极限」。

余极限：对偶到 `F^op` 的极限（文件后部注释写明）。

### 专项结构（同一 UMP 的特化）

| 文件 | 形状直觉 |
|------|----------|
| `Structure/Equalizer.v` | 两条平行箭的等化 |
| `Structure/Pullback.v` | 拉回方块 |
| `Structure/Complete.v` | 「所有（某类）极限存在」 |
| `Structure/Limit/Kan/...` | 极限与 Kan 扩张的关系 |

读专项文件时，心里翻译成：`J` 是什么、腿是什么、中介箭头叫什么。

## 典型 Goal

UMP 证明常分裂为：

1. **构造** `u`（用 fork、配对、或已有极限的中介）；
2. **验证** 每条腿 `vertex_map ∘ u ≈ …`；
3. **唯一性**：假设另一 `u'` 也行，证 `u ≈ u'`（常用各腿投影后用 mono 或再调 UMP）。

Goal 里看到一长串 `vertex_map`，先画图再写证明。

## 易混对比

| 易混 | 分清 |
|------|------|
| 锥 vs 极限锥 | 锥很多；极限是带 UMP 的那个 |
| 极限 vs colimit | 箭头方向／对偶；不要混 `inl` 与 `exl` |
| 「极限是对象」 | 对象 + 腿 + UMP；单说对象会丢结构 |
| Kan 扩张 vs 极限 | 极限可看成某种 Kan；但 [10](10-monoidal-kan-ends.md) 的 Kan 更一般（沿任意函子延拓） |

## CoqIDE 步骤

1. 打开 `Structure/Cone.v`，弄清 `vertex_obj` / `vertex_map` / `Cocone`。
2. 打开 `Structure/Limit.v` 的 `Class Limit`，朗读 `ump_limits` 一句中文。
3. 打开 `Structure/Equalizer.v` 或 `Pullback.v`，对照「特化 UMP」与一般 `Limit`。
4. 回到 `Structure/Cartesian.v` 的 `ump_products`，说明它为何是极限 UMP 的特例。
5. （可选）浏览 `Structure/Complete.v` 的陈述，不要急着读完证明。

## 相关笔记

极限与 Kan 的衔接见笔记 [Kan 扩展](https://github.com/exsabersac/haskell-algebra-notes) 目录；本教程 [10](10-monoidal-kan-ends.md) 会再接一次。

下一篇：[07 Yoneda](07-yoneda.md)
