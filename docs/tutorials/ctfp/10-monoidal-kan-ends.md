# 10 · 幺半范畴、Kan 扩张与 End / Profunctor

**CTFP**：约 3.10–3.12（Ends、Kan、充实/张量相关）。  
**DaoFP**：约 §18 Profunctor、§20 Kan。  
**笔记**：[幺半范畴](https://github.com/exsabersac/haskell-algebra-notes)、[Kan 扩展](https://github.com/exsabersac/haskell-algebra-notes)；Optics 后续可接 End。

本篇三节独立可读；建议顺序：幺半 → Kan → End。

---

## A. 幺半范畴

### 机制

范畴 `C` 带张量 `⊗ : C × C → C`、单位对象 `I`，以及结合子、左右单位子等**连贯同构**（Mac Lane 连贯性：所有合法图交换）。

特例：

- **笛卡尔幺半**：`⊗ = ×`，`I = 1`（有投影/对角）；
- **End 上的复合**：自函子合成是幺半，其 monoid 对象恰是 Monad（回 [09](09-monad-algebra.md)）。

### 本库

- `Structure/Monoidal.v`：`Class Monoidal`
- `Structure/Monoidal/*`：对称、闭幺半、Heunen–Vicary 笛卡尔幺半等变体
- `Structure/Monoid.v` / `Theory/Algebra/Monoid.v`：monoid **对象**（在已有幺半结构里）

读 `Monoidal` 时盯：张量的函子性、单位子、五边形/三角形义务落在哪些字段。不要与 `Cartesian` 混用字段名。

### 短例子

```haskell
-- 笛卡尔：(a,b) 张量，() 单位
-- 列表拼接是 monoid：[] 与 (++)
-- Monad：fmap 复合当 ⊗，Id 当 I，ret/join 当 monoid 结构
```

### 易混

| 笛卡尔 `×` | 一般 `⊗` |
|------------|----------|
| 有 `exl`/`exr`/对角 | 一般没有规范投影 |
| CCC 走 `Cartesian/Closed` | 闭幺半走 `Monoidal/Closed` |

---

## B. Kan 扩张

### 机制

沿函子 `K : A ⟶ B`「延拓」`F : A ⟶ C`：

- **左 Kan** `Lan_K F`：最「自由」的延拓（左伴随于预复合）；
- **右 Kan** `Ran_K F`：最「强制」的延拓（右伴随于预复合）。

预复合 `− ◯ K : [B,C] ⟶ [A,C]`；当伴随存在时，左/右伴随就是 Lan/Ran。

极限/余极限、伴随自身、密度、神经实现……许多构造是 Kan 的特例。笔记「左伴随作为 Kan」即此观点。

### 本库：`Theory/Kan/Extension.v`

```coq
Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ◯ F;   (* 注意：文件里延拓所沿函子名是 F *)
  fmap := fun _ _ f => {| transform := fun z => transform[f] (F z) |}
|}.

Class RightKan := { … }  (* 右 Kan：Induced 的右伴随数据 *)
(* 左 Kan 对偶/并列定义于同文件后文 *)
```

先读懂 `Induced`（预复合），再读 `RightKan`/`LeftKan` 的单位—余单位或 Hom 陈述。`Structure/Limit/Kan/` 把极限接回 Kan 语言。

### 短例子

- 沿嵌入延拓离散图 → 与（余）极限相关；
- 密度公式：`Lan ≅ coend` 形状（与下节 End/Coend 相连）；
- Haskell 里 Kan 常出现在「把限制在子类上的函子延拓出去」的优化/编码（Hinze 等）；本库偏数学定义。

### 易混

| Kan 扩张 | 极限 |
|----------|------|
| 延拓的是**函子** | 极限吃的是图 `J⟶C` |
| 一般沿任意 `K` | 极限 ≈ 沿特定形状的 Kan |

---

## C. End / Coend / Profunctor

### 机制

Profunctor `P : C^op × D → Sets`（或充实版）上：

- **End** `∫_c P(c,c)`：双变元的「极限式」——对对角两端自然的 dinatural 族的万有端；
- **Coend** `∫^c P(c,c)`：对偶的「余极限式」。

编程/optics：`Iso`、`Lens` 等常用 profunctor 编码；Day 卷积用 coend 定义函子张量。见 `Construction/Day.v`、`Theory/Profunctor.v`、`Theory/Dinatural.v`。

### 本库

| 文件 | 内容 |
|------|------|
| `Structure/End.v` | End |
| `Structure/Coend.v` | Coend |
| `Theory/Profunctor.v` | Profunctor |
| `Theory/Dinatural.v` | dinatural 变换 |
| `Construction/Day.v` | Day 卷积 |

读 End 定义时，抓住：**不是普通自然变换**，而是 dinatural（两端同变元时方向相反）。这是与 [05](05-natural.md) 的分界。

### 缺口声明

Ends → Optics 的范畴侧桥，笔记有 Optics By Example 摘要，本教程不展开实现；把 End/Profunctor 字段读懂即可接到笔记。

---

## CoqIDE 步骤（分三次做完）

**幺半**

1. `Structure/Monoidal.v`：解释 `Class Monoidal` 数据字段与一两个连贯义务。  
2. 对照 `Structure/Cartesian.v`：列出「笛卡尔多出来的投影」。  
3. `Monad/Monoid.v` 或 `Theory/Algebra/Monoid.v`：看 Monad↔monoid 的方向。

**Kan**

4. `Theory/Kan/Extension.v`：先解释 `Induced`，再进入 `RightKan`。  
5. 扫 `Structure/Limit/Kan/` 文件名，建立「极限 ⊆ Kan 故事」印象。

**End**

6. `Theory/Dinatural.v` 与 `Structure/End.v` 各读定义段。  
7. （选）`Construction/Day.v` 看 coend 出现位置；`Theory/Profunctor.v` 看类型形状。

## 相关笔记

- [幺半范畴](https://github.com/exsabersac/haskell-algebra-notes)  
- [Kan 扩展](https://github.com/exsabersac/haskell-algebra-notes)  
- Optics 目录（Ends 应用）

下一篇：[11 Lawvere 与 Free](11-lawvere-free.md)
