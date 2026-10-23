# 11 · Lawvere 理论与 Free / 初始代数

**CTFP**：约 3.14 / Lawvere theories 相关章。  
**DaoFP**：代数/自由侧章节。  
**笔记（重点）**：[Lawvere 理论](https://github.com/exsabersac/haskell-algebra-notes)、[初始代数](https://github.com/exsabersac/haskell-algebra-notes)、[Free](https://github.com/exsabersac/haskell-algebra-notes)；demo：`src/Lawvere/Demo.hs`。

## 两条线，一个汇合点

1. **Lawvere 理论**：用「保有限积的范畴」编码代数签名；模型 = 保积函子；与 finitary monad 对应。  
2. **Free / 初始代数**：用初始 F-代数或自由 Monad 生成「语法树 + fold」。

两者都在说「运算 + 等式 + 解释」；本库分别落在 `Theory/Lawvere*` 与 `Construction/FAlg`/`Free`。

---

## A. Lawvere 理论（本库怎么写）

### 机制（陈述）

经典图像：

- 理论 `L`：有限积范畴，对象由自然数（元数）生成，`n` 扮演「n 元组」；
- 态射 `m → n` 扮演「n 个 m-元导出运算」；
- **模型**：保有限积函子 `L ⟶ Sets`（或别的有积范畴）；
- 平凡理论（只有积结构、无额外运算）的模型范畴等价于集合范畴本身——笔记里已讲过 `Mod(F^op,Set)≃Set` 这类事实。

Finitary monad ↔ Lawvere：有限元代数理论与有限秩单子互通（CTFP / 笔记「与 finitary-monad」文）。

### 本库：`Theory/Lawvere.v`

```coq
Class LawvereTheory : Type := {
  law_cat : Category;
  law_terminal : @Terminal law_cat;
  law_cartesian : @Cartesian law_cat;

  law_of_nat : nat → law_cat;
  law_zero_terminal :
    law_of_nat 0%nat = terminal_obj;
  law_plus_product : ∀ m n,
    product_obj (law_of_nat m) (law_of_nat n) = law_of_nat (m + n)%nat
}.
```

读法：

- 理论首先是一个**带有限积**的范畴；
- `law_of_nat` 把元数嵌进对象；
- `0` 必须是终对象，`m+n` 必须是积——用定义等式 `=` 钉在结构上（注意：这里是对象级 `=`，与态射 `≈` 不同）。

`law_pow`：用反复积 `1×1×…` 实现 `n`，并证明与 `law_of_nat n` 相同。

相关文件：

| 路径 | 内容 |
|------|------|
| `Theory/Lawvere/Model.v` | 模型（保积函子） |
| `Theory/Lawvere/Monad.v` | 与 monad 的桥 |
| `Theory/Lawvere/PROP.v`、`Sets.v` | 变体 / Sets 上情况 |
| `Instance/FinSet/Lawvere.v` | FinSet 侧实例 |

### 短例子

Monoid 理论：对象 `n`，除积结构外，还有态射编码 `μ : 2→1`、`η : 0→1` 及结合/单位等式（作为交换图）。  
模型：选集合 `X`，把 `μ` 解释为 `X×X→X`，即 monoid 乘法。

Haskell demo 见笔记仓库 `src/Lawvere/Demo.hs`——先跑通直觉，再回 Coq 字段。

### 易混

| Lawvere 理论 | Monad / EM |
|--------------|------------|
| 用**有限积范畴**编码运算 | 用自函子+η/μ |
| 模型是**保积函子** | EM 代数是 `T a ~> a` |
| 与 **finitary** monad 对应 | 一般 Monad 可更「大」 |

---

## B. Free 与初始代数（接 [09](09-monad-algebra.md)）

### 机制

- 初始 F-代数 `μF`：语法；`cata`：唯一语义箭头。  
- `Free_F(X) ≈ μY. (X + F Y)`：在叶子处挂 `X` 的自由结构。  
- `foldFree` / 解释器 ≈ 某次 cata。

Lambek：初始代数的结构映射是同构（「滚动/展开」）。  
Adamek：在合适条件下用 ω-链胶体构造 `μF`。

### 本库路径

| 路径 | 作用 |
|------|------|
| `Construction/FAlg.v` | F-代数范畴 |
| `Construction/FCoalg.v` | 对偶余代数 |
| `Construction/Free.v` | Free 构造入口 |
| `Theory/Lambek.v` | Lambek |
| `Theory/Adamek.v` | Adamek |
| `Theory/Recursion.v` | 递归/迭代相关 |

与 Lawvere 汇合的直觉：自由模型函子往往是某遗忘的左伴随；生成的 monad 若 finitary，则对应某 Lawvere 理论。细节读 `Theory/Lawvere/Monad.v` + 笔记「多种 finitary-monad」。

---

## CoqIDE 步骤

1. 打开 `Theory/Lawvere.v`，解释 `LawvereTheory` 五个字段；弄清为何 `law_zero_terminal` 用 `=`。  
2. 看 `law_pow` / `law_pow_one`：元数对象的两种写法一致。  
3. 打开 `Theory/Lawvere/Model.v`，找到「模型」类型声明，对照笔记「模型」文。  
4. 打开 `Instance/FinSet/Lawvere.v` 扫实例声明。  
5. 切换到 `Construction/FAlg.v` + `Theory/Lambek.v`，用 [09](09-monad-algebra.md) 的表再核对一遍「不是 EM」。  
6. （选）`Construction/Free.v` 看 Free 暴露的定义名；对照笔记 Free 目录。

## 相关笔记（建议对照阅读）

- [docs/Lawvere理论/](https://github.com/exsabersac/haskell-algebra-notes)  
- [docs/初始代数/](https://github.com/exsabersac/haskell-algebra-notes)  
- [docs/Free/](https://github.com/exsabersac/haskell-algebra-notes)

下一篇：[12 Sets · Cat · Coq 实例](12-instances.md)
