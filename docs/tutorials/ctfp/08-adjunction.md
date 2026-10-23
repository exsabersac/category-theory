# 08 · 伴随函子

**CTFP**：约 3.2–3.3（伴随相关章）。  
**DaoFP**：`10-Adjunctions` 一带。  
**笔记**：Kan「左伴随作为左/右 Kan」相关讨论见 [haskell-algebra-notes · Kan](https://github.com/exsabersac/haskell-algebra-notes)。

## 这个概念在干什么

两个函子 `F : D ⟶ C`（左）与 `U : C ⟶ D`（右）构成伴随 `F ⊣ U`，当存在自然的双射：

```text
C(F x, y)  ≃  D(x, U y)
```

左边一条箭「转置」成右边一条箭，来回几乎互逆，且对 `x,y` 都自然。

伴随弱于等价，却强到能**搬运极限/余极限、制造 Monad、刻画自由-遗忘**。Mac Lane 的评价是：伴随无处不在。

## 三种等价面孔（本库都有）

| 面孔 | 本库落点 | 直觉 |
|------|----------|------|
| Hom-集同构 `adj` | `Theory/Adjunction.v` 的 `Class Adjunction` | 转置 ⌊−⌋ / ⌈−⌉ |
| 单位 η / 余单位 ε + 三角 | `Adjunction/Natural/Transformation.v` 等 | `return` / `extract` 味 |
| 万有箭头 | `Theory/Universal/Arrow.v`；GAFT 引擎 | 「自由对象」逐点 |

本篇精读 **hom-集形式**；另外两种知道入口即可。

## 短例子

```text
自由遗忘：List ⊣ 遗忘（Monoid→Set）等
柯里化： (− × A) ⊣ (−)^A
对角 ⊣ 积： Δ ⊣ ×
Galois 联络：偏序上的伴随（Instance/Proset/Galois.v）
```

Haskell 直觉：`leftAdjunct` / `rightAdjunct` 对应转置；`unit`/`counit` 特殊化后像 `return`/`extract`（随具体伴随而变）。

## 本库：`Theory/Adjunction.v`

```coq
Class Adjunction := {
  adj {x y} :
    Isomorphism Sets
      {| carrier := hom C (F x) y; … |}
      {| carrier := hom D x (U y); … |}
    where "⌊ f ⌋" := (to adj f)
      and "⌈ f ⌉" := (from adj f);

  to_adj_nat_l   … : ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  to_adj_nat_r   … ;  (* 经 U 的自然性 *)
  from_adj_nat_l … ;
  from_adj_nat_r … ;
}.
```

### 字段怎么读

- `adj`：对每对对象，把 `F x ~> y` 与 `x ~> U y` 当成 **Sets 里的同构**（两边 carrier 是 hom-setoid）；
- ⌊f⌋ = `to adj f`：左转右；⌈f⌉ = `from adj f`：右转左；
- `to_adj_nat_*` / `from_adj_nat_*`：转置对两个变元的自然性——少一条，Yoneda/复合图就会裂。

派生：

- `unit` η := ⌊id⌋ : `x ~> U (F x)`；
- `counit` ε := ⌈id⌉ : `F (U y) ~> y`；
- 三角恒等式：`counit_fmap_unit`、`fmap_counit_unit`（文件中作推论）。

### 典型 Goal

证明两个转置相等时，常：

1. 利用 `adj` 是同构（`iso_to_from`）；
2. 或把等式「搬到另一侧」再比；
3. 自然性义务展开后变成 `fmap` 与 `∘` 的重写，类似自然变换证明。

## 伴随诱导 Monad

Huber：每个 `F ⊣ U` 给自函子 `U ∘ F` 套上 Monad 结构——本库 `Monad/Adjunction.v` 的 `Adjunction_Monad`。  
逆方向：每个 Monad 来自伴随——Kleisli（初始）与 Eilenberg–Moore（终结）两种分解，见 [09](09-monad-algebra.md)。

右伴随保极限、左伴随保余极限：`Adjunction/Continuity.v`。

## 易混对比

| 易混 | 分清 |
|------|------|
| 左 / 右伴随 | `F` 左、`U` 右；Hom 里 `F` 在左边变元 |
| 伴随 vs 逆函子 | 逆是更强；伴随只要求 Hom 自然双射 |
| η/ε 形式 vs Hom 形式 | 等价；本库以 Hom 为原始，η/ε 派生或见 Transform 版 |
| 「自由」一定是左伴随 | 自由-遗忘模式常见，但伴随不都叫自由 |

## CoqIDE 步骤

1. 打开 `Theory/Adjunction.v`，读文首中文导言里的三种形式地图。
2. 解释 `Class Adjunction` 至自然性字段；确认 ⌊⌋ / ⌈⌉ 记号。
3. 找到 `unit`/`counit` 与三角推论的陈述并试着口述证明 sparke。
4. 打开 `Monad/Adjunction.v`，看 `ret`/`join` 如何用 η、ε、`F`、`U` 拼出。
5. （可选）`Adjunction/Diagonal/Product.v`：积作为伴随——把 [02](02-products.md)、[03](03-closed.md) 与本篇焊住。
6. （可选）`Adjunction/GAFT.v`：只需知道「伴随函子定理在这里」，不必首通读完。

下一篇：[09 Monad 与两种代数](09-monad-algebra.md)
