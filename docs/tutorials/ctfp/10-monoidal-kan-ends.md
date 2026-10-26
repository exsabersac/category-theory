# 10 · 幺半范畴、Kan 扩张、Ends / Profunctor

**CTFP**：3.10 *Ends and Coends*；3.11 *Kan Extensions*；3.12 *Enriched Categories*；3.15 *Monads, Monoids and Categories*。  
**DaoFP**：`18-Ends`、`20-Kan`（§19 Tambara/Optics 为缺口）、`21-Enrichment`；§5 中 Monoidal 引言。

> 原创教学复述。对读笔记 [幺半范畴](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/%E5%B9%9A%E5%8D%8A%E8%8C%83%E7%95%B4)、[Kan扩展](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/Kan%E6%89%A9%E5%B1%95)。

## 1. 书侧三条线

**幺半范畴**：`⊗`、单位、连贯。单对象≈幺半群；`([C,C],∘,Id)` 的 monoid 对象≈Monad（3.15 精神）。

**Ends / Profunctor**：`C^op×D⟶Set`；End≈对角极限式；Nat 可写 End；Day/optics 常用 coend。

**Kan**：沿 `K` 最佳延拓 `Ran`/`Lan`；局部 UMP；全局常 `Induced ⊣ Ran`；极限是特例；左伴随可写为某右 Kan（笔记已有）。

## 2. 本库路径

| 主题 | 路径 |
|------|------|
| 幺半 | `Structure/Monoidal*`；`Theory/Algebra/Monoid.v` |
| End/Coend | `Structure/End.v`、`Coend.v` |
| Profunctor/Dinatural | `Theory/Profunctor.v`、`Dinatural.v` |
| Day | `Construction/Day.v` |
| Kan | `Theory/Kan/Extension.v`；`Structure/Limit/Kan/*` |

```coq
Class RightKan := { Ran : [A,C]⟶[B,C]; ran_adjoint : Induced ⊣ Ran }.
Class LocalRightKan (X) := {
  LocalRan : B⟶C; ran_transform : LocalRan◯F ⟹ X;
  ump_ran M μ : ∃! δ, μ ≈ ran_transform ∙ δ ⊲ F
}.
```

## 3. CoqIDE 证明走读

### 3.1 Monoidal

识别 tensor、单位、结合子/单位子。大 `≈` Goal 先试 `cat`，再对张量 functoriality 重写。

### 3.2 End

楔 / dinatural UMP。方程≈「两端复合相等」。对照自然性，多反变端。

### 3.3 `RightKan_to_LocalRightKan`

用 `from adj nat_id` 造 counit；Obligation 出现 `from_adj_nat_l`、`iso_from_to`——复习 [08](08-adjunction.md)。跟至少一条 Obligation。

### 3.4 Day

`Construction/Day.v`：指认 coend；Obligation 常 dinatural 重排。第一次能指认即可。

## 4. 口诀（导航用，非替代证明）

- `Nat(F,G) ≅ ∫ Hom(Fc,Gc)`  
- 右 Kan 的 end 公式（精神）  
- `lim ≅ Ran` 沿到终范畴  

充实：E-category≈充实到 setoid；真 V-enriched 更重。

## 5. 易混 / 清单

End≠玩积分号；Kan 需假设；Optics 缺口。  
检查：Monoidal 字段；End UMP；`ump_ran`；Kan 转换 Obligation；笔记 UP 文对照。



## 6. 幺半：书侧 + 本库加厚

CTFP 3.15 与笔记「是不是幺半群」「自由幺半群与列表」共同指出：Monad 是自函子范畴里的 monoid。读 `Structure/Monoidal.v` 时：

1. 找出 `tensor`、`unit_obj`；  
2. 找出结合子、左/右单位子字段名；  
3. 找一条连贯性定理，看 Goal 有多少个 `⊗`；  
4. 问：若 `⊗` 取 `∘`、单位取 `Id`，字段是否像 Monad 定律？

笛卡尔积是特殊幺半；CCC 的指数是相对积张量的内齐 Hom——回 [03](03-closed.md)。

## 7. Ends：书侧 + IDE

DaoFP §18 / CTFP 3.10：从 profunctor 到 end。本库：

1. 打开 `Structure/End.v`，找 wedge / dinatural 条件；  
2. 找 UMP（普遍楔）；  
3. 打开 `Theory/Dinatural.v` 对照「比自然性多反变端」；  
4. `Theory/Profunctor.v` 扫 `Class` 名。

口念：`Nat(F,G)` 像 `∫ Hom(Fc,Gc)`——再在库里找是否形式化了该同构。

## 8. Kan：书侧 + IDE 加厚

1. 读笔记「定义与UP」标题与定义框（不抄长文）。  
2. 打开 `Theory/Kan/Extension.v`，对照 `LocalRightKan`。  
3. 逐步 `RightKan_to_LocalRightKan` 第一条 Obligation：标出 `adj` 出现处。  
4. 读笔记「左伴随作为右Kan」：用本课语言复述一句。  
5. `Structure/Limit/Kan/` 列出文件名，标哪个接 [06](06-limits.md)。

## 9. Day / Optics 缺口

`Construction/Day.v` 指认 coend。Optics / Tambara（DaoFP §19、笔记 Optics）标为后续加厚，本课只要求：知道 Ends/Profunctor 是入口。

## 10. CoqIDE 检查清单（扩）

1. [ ] Monoidal 字段表自填。  
2. [ ] End 或 Coend UMP。  
3. [ ] Dinatural 与 natural 一句对比。  
4. [ ] `ump_ran` 解释。  
5. [ ] Kan 转换至少一Obligation。  
6. [ ] Day 文件指认 coend。  
7. [ ] 笔记三篇 Kan/幺半打开过。




## 11. 综合例子：从「Nat 是 end」想到本库该打开谁

书侧常说自然变换集合是某种 end。落地检查清单：

1. 打开 `Theory/Natural/Transformation.v` 确认变换 setoid；  
2. 打开 `Structure/End.v` 看 end 的对象是否声明为某 Setoid/Sets 对象；  
3. 搜 `Nat`/`Transform`/`End` 同时出现的引理；  
4. 若尚无完整同构，记下「缺口」——教程不假装库里有而未形式化的定理。

这是诚实读库的态度：书负责直觉，库负责已证部分，缺口显式标明。


下一篇：[11 Lawvere 与 Free](11-lawvere-free.md)
