# 07 · Yoneda 引理与可表函子

**CTFP**：约 2.4–2.6（Yoneda 相关章）。  
**DaoFP**：多在自然变换/可表附近提及。  
**笔记**：Yoneda 专题偏薄——本篇补机制；读完可反哺 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

## 这个概念在干什么

一句话：

> 预层 `F` 在对象 `A` 上的值，等于从可表预层 `Hom(−,A)` 到 `F` 的自然变换。

形式（反变 Yoneda，Sets 值）：

```text
Nat( Hom(−, A) , F )  ≃  F A
```

正向读：要知道 `F A`，等价于知道所有「探针」`Hom(X,A)` 如何被 `F` 作用后与 `F X` 交互的自然方式。  
口号：**对象由它发出/接收的箭头刻画**——与第 01 篇「不看对象内部」一脉相承。

## 短例子（编程）

```haskell
-- 固定 a，自然变换 Hom(a, –) ⟹ F 的分量在 id 处取值：
--   η_a (id) ∈ F a
-- 反过来，给 y ∈ F a，定义
--   η_x (f : a -> x) = fmap f y
```

`Coyoneda` / 表示引理在 Haskell 优化里常见：把 `fmap` 积攒成「存在一个 b 与 b→a 与 F b」。本库是数学陈述优先，但同一双向构造。

## 本库路径

| 路径 | 作用 |
|------|------|
| `Functor/Hom.v` | hom 函子（可表的原材料） |
| `Functor/Hom/Yoneda.v` | Yoneda 引理主陈述 `Yoneda_Lemma` |
| `Functor/Hom/Yoneda/Iso.v`、`Natural.v` | 同构/自然性细化 |
| `Theory/Universal/Element.v` | 万有元视角 |
| `Theory/Coend/Yoneda.v` | coend 形式的 Yoneda |

主文件中的实例（简化阅读）：

```coq
Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) :
  ∀ A : C, Presheaves [Hom ─,A] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi => fmap[F] phi y |} |} |}
}.
```

### 两个方向在干什么

**`to`（自然变换 → 元）**  
取自然变换 `x : Hom(−,A) ⟹ F`，看它在对象 `A`、态射 `id : A ~> A` 上的分量：`transform[x] A id`，得到 `F A` 的元。

**`from`（元 → 自然变换）**  
给定 `y : F A`，在每个 `X` 上把 `phi : A ~> X`（注意 `C^op` 方向）送到 `fmap[F] phi y`。自然性靠 `F` 的 `fmap_comp`。

往返证明在 `Next Obligation` 里：一边用 `fmap_id` 收回 `y`，另一边用自然性把任意分量写成「先 `id` 再 `fmap`」。

### 你在 Goal 里会看到什么

- `Presheaves` / `Sets`：相等是点点或 setoid 态射相等；
- `transform[…]`：自然变换分量；
- 大量 `fmap` 与 `naturality`——Yoneda 证明几乎是自然性的习题课。

## 可表函子

`F` **可表**，若存在 `A` 使 `F ≅ Hom(−,A)`（或共变 `Hom(A,−)`）。  
Yoneda 嵌入 `A ↦ Hom(−,A)` 全忠实：对象之间的箭头 ↔ 可表预层之间的自然变换。这保证「只看箭头」的世界观是忠的。

## 易混对比

| 易混 | 分清 |
|------|------|
| 共变 vs 反变 Yoneda | 本主文件对 `C^op ⟶ Sets`；共变版对偶/另述 |
| Yoneda 引理 vs Yoneda 嵌入 | 引理是 `Nat(Hom(−,A),F)≃F A`；嵌入是 `A↦Hom(−,A)` 这个函子 |
| 「`F A` 的元素」 | 在 `Sets` 实例里真是 carrier 的元；一般预层要按 Sets 结构读 |
| CoYoneda / coend 形式 | 见 `Theory/Coend/Yoneda.v`；先掌握引理双向再读 |

## CoqIDE 步骤

1. 先打开 `Functor/Hom.v`，确认 `Hom` 函子的 `fobj`/`fmap`（反变在哪一臂）。
2. 打开 `Functor/Hom/Yoneda.v`，定位 `Yoneda_Lemma`。
3. 逐步解释 `to` 与 `from` 的 Program 定义；每个 `Next Obligation` 用一句话概括在证什么（Proper / 自然性 / fmap_id / 往返）。
4. 打开 `Yoneda/Natural.v` 或 `Iso.v`，看引理如何被包装成更易用的同构。
5. （可选）`Theory/Universal/Element.v`：用「万有元」语言复述同一事实。

## 相关笔记

建议在 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 补一篇 Yoneda 短文：Haskell `Coyoneda` ↔ 本文件 `from`/`to`。当前笔记以 Kan/Lawvere/初始代数更厚。


## 把引理当成「计算规则」

**计算 `to ∘ from`**：从元 `y` 造出自然变换，再在 `id` 处取样 → 应回到 `y`。关键等式是 `fmap id y ≈ y`，即 `fmap_id`。

**计算 `from ∘ to`**：从自然变换 `η` 取出 `η_A(id)`，再定义 `φ ↦ fmap φ (η_A(id))`。自然性说：

```text
η_X(φ) ≈ fmap φ (η_A(id))
```

（φ 看作从 A 出去的箭时的标准 Yoneda 计算。）于是任意分量被「id 分量 + fmap」重建——这就是为什么自然变换被一个元完全决定。

### 嵌入全忠实（意义）

Yoneda 嵌入 `よ : C ⟶ [C^op, Sets]`，`よ(A) = Hom(−,A)`。  
全忠实大意：`C(A,B)` 与 `Nat(よ A, よ B)` 同构。  
于是「只讨论预层与自然变换」时，仍能无损取回对象之间的箭。这是「箭头世界观」的技术担保。

### 和笔记、Kan 的衔接

- 密度公式 / 余端形式：`Theory/Coend/Yoneda.v` 与 [10](10-monoidal-kan-ends.md)；  
- 表示引理在 Haskell 的 `Coyoneda f a = ∃ b. (b → a, f b)` ≈ 自由在 fmap 上的表示——建议写入 [haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes) 补缺口。

下一篇：[08 伴随](08-adjunction.md)
