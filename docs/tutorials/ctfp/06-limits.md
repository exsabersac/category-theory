# 06 · 锥与（余）极限

**CTFP**：2.2 *Limits and Colimits*。  
**DaoFP**：§9 中 Limits 相关讨论；后文将极限视为伴随 / Kan 特例（§10、§20）。

> 原创教学复述；不摘录书中正文。

## 1. 书侧故事：一张图上的「最佳顶点」

积、终对象、等化子、拉回……CTFP 2.2 把它们收成同一模式：

1. 指标范畴 `J` + 图 `F : J ⟶ C`；  
2. **锥**：顶点 + 到各 `F j` 的腿，且与 `F` 的箭头相容；  
3. **极限**：普遍锥——任意锥经唯一中介箭因子分解。

余极限 = 对偶（余锥的普遍性）。DaoFP 强调锥的相容性长得像自然性（常值函子 ⇒ `F` 的自然变换），并为「极限 = 右伴随 / 右 Kan」留接口。

## 2. 例子表（书侧常见）

| 名字 | 指标图 | 程序员直觉 |
|------|--------|------------|
| 终对象 | 空 | `()` |
| 积 | 两点离散 | `(a,b)` |
| 等化子 | 平行对 | `{x \| f x = g x}` |
| 拉回 | 共尾 cospan | join / 纤维积 |
| 余积 | 两点离散（余） | `Either` |
| 推出 | span 的余 | 黏合 |

## 3. 本库

### `Structure/Cone.v`

```coq
Class ACone {J C} (c : C) (F : J ⟶ C) := {
  vertex_map (x : J) : c ~> F x;
  cone_coherence {x y} (f : x ~> y) :
    fmap[F] f ∘ vertex_map x ≈ vertex_map y
}.

Class Cone (F : J ⟶ C) := {
  vertex_obj : C;
  coneFrom : ACone vertex_obj F
}.

Definition Cocone F := Cone (F^op).
```

### `Structure/Limit.v`

```coq
Class Limit (F : J ⟶ C) := {
  limit_cone : Cone F;
  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x,
    vertex_map[limit_cone] ∘ u ≈ vertex_map[N] x
}.
```

`IsALimit F c`：断言对象 `c` 带着锥是极限。专项文件：`Equalizer.v`、`Pullback.v` 等。

## 4. CoqIDE 证明走读

### 4.1 建锥的 Obligation

Goal 常是 `cone_coherence`：对 `f : x ~> y` in `J`，

```text
fmap[F] f ∘ vertex_map x ≈ vertex_map y
```

证法：展开腿定义，用 `F` 的 `fmap_comp`/`fmap_id`，必要时 `cat`。

### 4.2 使用 `ump_limits`

```coq
destruct (ump_limits N) as [u [Hu Unique]].
(* Hu : 腿方程；Unique : 任何其它中介 ≈ u *)
```

证两个中介相等：证它们对每个腿复合后都满足同一族方程，再 `apply Unique`。

### 4.3 极限顶点同构唯一（精神）

与 `terminal_unique` 同模板：双向 UMP 得 `u,v`，再 `u∘v≈id`（两者都是自中介）。CoqIDE 若有现成定理，跟 Proof；若无，在纸上写模板即可。

### 4.4 Equalizer / Pullback

打开其一：识别数据字段（平行箭 / cospan）与 UMP。把 `ump_products` 的「投影方程」替换成「等化方程」或「拉回方块」，心理模型就通了。

### 4.5 积作为极限

若有定理「离散两点的极限 = 积」，对照 `ump_limits` 与 `ump_products`：指标变了，唯一性没变。

## 5. 书侧加厚：和伴随 / Kan 的一句话

常值函子 `Δ : C ⟶ [J,C]` 的右伴随（若存在）送出极限；左伴随送出余极限。右 Kan 沿 `J → 1` 亦然。细节 [08](08-adjunction.md)、[10](10-monoidal-kan-ends.md)；本篇先把 `ump_limits` 钉牢。

## 6. 易混对比

| 说法 | 澄清 |
|------|------|
| 任意锥是极限 | 要普遍性 |
| 极限对象字面唯一 | 仅同构唯一 |
| 余极限另套理论 | `F^op` |
| 有积+等化子⇒完备 | 经典元定理；是否形式化以库为准 |

## 7. CoqIDE 检查清单

1. [ ] 解释 `cone_coherence`。  
2. [ ] 解释 `∃!` in `ump_limits`。  
3. [ ] 看 `Cocone` 一行定义。  
4. [ ] Equalizer 或 Pullback 走读 UMP。  
5. [ ] 口述「极限同构唯一」模板。  
6. [ ] 扫 `Structure/Limit/Kan/` 目录名。



## 8. 更细的 CoqIDE 会话

### 会话 A：读锥

1. 打开 `Structure/Cone.v`。  
2. 解释 `ACone`：只有腿 + 相容，无普遍性。  
3. 解释 `Cone`：打包顶点。  
4. 看 `Cocone` 定义，画 `F^op` 箭头反转草图。

### 会话 B：读极限 UMP

1. 打开 `Structure/Limit.v`。  
2. 对 `ump_limits` 用 `Check` / 文档悬停看完整类型。  
3. 在纸上展开 `∃! u`：存在 + 唯一。  
4. 搜 `ump_limits` 的使用处（`Search` 或 ripgrep），跟一处 `destruct`。

### 会话 C：Equalizer

1. 打开 equalizer 文件。  
2. 列出：平行的 `f,g`、对象 `Eq`、嵌入 `e`、UMP 字段名。  
3. 对比积的 `ump_products`：方程从「投影还原」变成「`f∘e≈g∘e`」。  
4. 任选一条 Corollary，看是否只用 UMP 不展开 Sets。

### 会话 D：与终对象模板对照

重读 [02](02-products.md) 的 `terminal_unique`，写下「极限同构唯一」四步，两份对照。这是范畴论证明的标准肌肉记忆。

## 9. 书侧对照（CTFP 2.2）

| 书中图例（标题级） | 本库 |
|--------------------|------|
| 终/积 | Terminal/Cartesian + 视为极限 |
| 等化子 | Equalizer |
| 拉回 | Pullback |
| 余极限 | Cocone / Colimit |
| 「极限是伴随」预告 | [08](08-adjunction.md)、[10](10-monoidal-kan-ends.md) |


下一篇：[07 Yoneda](07-yoneda.md)
