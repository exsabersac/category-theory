# 07 · Yoneda 引理与可表函子

**CTFP**：2.4 *Representable Functors*；2.5 *The Yoneda Lemma*；2.6 *Yoneda Embedding*。  
**DaoFP**：`9-NaturalTransformations` 后半（Representable、guessing game）；编程侧常见 Yoneda 编码直觉。

> 原创教学复述；不摘录书中正文。笔记 Yoneda 偏薄——本篇写厚。

## 1. 书侧故事

### 可表函子

预层 `F : C^op ⟶ Sets` **可表**，若存在对象 `A` 与自然同构 `F ≅ Hom(−, A)`。CTFP 用「猜 `A`」说明：若你掌握 `F` 与所有测试对象的自然交互，你就在指认 `A`。DaoFP 的 guessing game 同一精神。

### Yoneda 引理

对任意预层 `F` 与对象 `A`：

> `Nat(Hom(−,A), F) ≅ F(A)`

- 左→右：自然变换 `η` 交给 `η_A(id_A)`；  
- 右→左：元素 `y ∈ F(A)` 生成 `phi ↦ F(phi)(y)`。

### Yoneda 嵌入

`A ↦ Hom(−,A)` 给出满忠实函子 `C ⟶ [C^op, Sets]`。对象之间的态射完全反映到预层范畴——「只谈箭头」方法论的定理版。

### 程序员口译

理想化下 `∀ x. (a -> x) -> f x` 与 `f a` 同构（Yoneda 编码）。可积攒 `fmap` 再一次性作用。严格 Hask 有底序；本库在 Sets 预层上形式化更干净。

## 2. 本库落点

- 主文件：`Functor/Hom/Yoneda.v`（`Yoneda_Lemma`）  
- 配套：`Functor/Hom/Yoneda/Iso.v`、`Natural.v`  
- 相关：`Theory/Universal/Element.v`、`Theory/Coend/Yoneda.v`

```coq
Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) :
  ∀ A : C, Presheaves [Hom ─,A] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x =>
                {| morphism := fun phi => fmap[F] phi y |} |} |}
}.
```

## 3. CoqIDE 证明走读（核心）

打开 `Yoneda.v`，解释 `Yoneda_Lemma`，**不要跳过 Obligation**。

| 约序 | 在维护什么 | 手段 |
|------|------------|------|
| Proper（transform） | `phi≈phi′` ⇒ fmap 相等 | `proper`；`fmap_respects` |
| 自然性 | 方块 | `destruct F`；`fmap_comp`；`symmetry` |
| naturality_sym | 另一朝向 | `fmap_comp` |
| from 的 Proper | 元素相等 ⇒ 变换相等 | `proper_morphism` |
| fmap_id 段 | `fmap id y ≈ y` | `fmap_id` |
| 闭合自然性 | 用 η 的自然性 | `rewrite naturality`；`cat` |
| to∘from / from∘to | 互逆 | `fmap_id`；对 id 取值 |

### 推荐节奏

1. 纸上写两向映射，不看 Coq。  
2. IDE 只读 `to`/`from` 数据结构。  
3. 逐条 Obligation，每条记一行笔记。  
4. 互逆向对照本节「精神计算」：  
   - `to(from y) = fmap id y ≈ y`；  
   - `from(to η)` 的分量用自然性改写成 `fmap phi (η id)`。

### 精神计算（from∘to）

`to η = η_A(id)`。`from` 之后在 `phi : A ~> x` 上的分量是 `fmap phi (η_A(id))`。自然性把 `η_x ∘ fmap[Hom] phi` 与 `fmap[F] phi ∘ η_A` 联系起来，而 `Hom` 的 fmap 是预复合，于是落到 `η_x(phi)`。逐步对上 Obligation 里的 `rewrite naturality`。

## 4. 嵌入与满忠实

读 CTFP 2.6 时记住本库目标：指出 `Yoneda` 嵌入函子，并找到 Full/Faithful 实例或定理（路径以源码为准）。满忠实 ⇒ 反映同构：若 `Hom(−,A) ≅ Hom(−,B)` 则 `A ≅ B`（在合适陈述下）。

## 5. 易混对比

| 说法 | 澄清 |
|------|------|
| Yoneda=fmap | 否；是 Nat≃元素 |
| 嵌入=等价 | 一般非本质满 |
| 共变版 | 对偶地陈述 |
| CPS 就是 Yoneda | 相关直觉；证明仍看自然性 |

## 6. CoqIDE 检查清单

1. [ ] 口述引理两向。  
2. [ ] 过完（可分次）全部 Obligation。  
3. [ ] 标出 `rewrite naturality` 出现处。  
4. [ ] 扫 Iso/Natural 配套。  
5. [ ] 回 [05](05-natural.md) 核对字段。  
6. [ ] （可选）Universal/Element。



## 7. 更细的 Obligation 跟踪表（打印着用）

复制下表，在 CoqIDE 过 `Yoneda_Lemma` 时打勾：

| # | Obligation 主题（自填） | 用到的引理/字段 | ✓ |
|---|-------------------------|-----------------|---|
| 1 | | | |
| 2 | | | |
| 3 | | | |
| 4 | | | |
| 5 | | | |
| 6 | | | |
| 7 | | | |
| 8 | | | |

若超过 8 条，继续加行。目标不是速度，是每条都能用中文说「这是在维护 Yoneda 的哪一半」。

## 8. 书侧对照（CTFP 2.4–2.6 × DaoFP representable）

| 主题 | 带走的一句话 | 下一步 |
|------|--------------|--------|
| Representable | F≅Hom(−,A) | 找普遍元 |
| Yoneda Lemma | Nat≃F(A) | 跟完 Obligation |
| Embedding | 满忠实嵌入 | Full/Faithful |
| Guessing game | 交互决定对象 | Universal element |
| 编程 Yoneda 编码 | 积攒 fmap | 直觉 only |

## 9. 与自然变换课的强制链接

若 [05](05-natural.md) 的会话 B（恒等变换）没做，先做再回来——Yoneda 的 `from` 方向构造的正是「由元素生成的自然变换」，自然性 Obligation 与会话 B 同源。


下一篇：[08 伴随](08-adjunction.md)
