# 11 · Lawvere 理论与 Free / 初始代数

**CTFP**：3.14 *Lawvere Theories*；旁及 2.3 *Free Monoids*、3.8 *F-Algebras*。  
**DaoFP**：`7-Recursion`、`11-Algebras`、`15-Monads`（Free monad 等）。

> 原创教学复述。强绑定笔记 [Lawvere理论](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/Lawvere%E7%90%86%E8%AE%BA)、[Free](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/Free)、[初始代数](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/%E5%88%9D%E5%A7%8B%E4%BB%A3%E6%95%B0)。

## 1. 书侧故事

**Lawvere 理论**：用有限积范畴编码签名；对象≈元数；模型=保积函子 `L⟶Set`；finitary monad↔理论（合适条件下）。平凡理论模型≃Set。Maybe 小品见笔记「副作用与Maybe」。

**初始代数 / Free**：`μF`+`cata`；Lambek；`Free_F(X)≈μY.(X+FY)`；`foldFree`≈某种 cata。

## 2. 本库 `Theory/Lawvere.v`

```coq
Class LawvereTheory := {
  law_cat : Category;
  law_terminal : Terminal; law_cartesian : Cartesian;
  law_of_nat : nat → law_cat;
  law_zero_terminal : law_of_nat 0 = 1;
  law_plus_product : m×n 的积对象 = law_of_nat (m+n)
}.
```

严格 `=` 钉死元数与积（与弱≅版本不同）。配套 `Lawvere/{Model,Monad,PROP,Sets}.v`、`Instance/FinSet/Lawvere.v`。

### `law_pow_one` 走读

```coq
Fixpoint law_pow n := match n with O=>1 | S k=>1×law_pow k end.
Theorem law_pow_one n : law_pow n = law_of_nat n.
Proof.
  induction n; simpl.
  - symmetry; apply law_zero_terminal.
  - rewrite IHn; apply (law_plus_product 1 n).
Defined.
```

CoqIDE 逐步：零元用 `law_zero_terminal`；归纳步 `rewrite IH` 后 `law_plus_product`。稀有的对象级 `=` 练习。

## 3. Free / FAlg

`Construction/FAlg.v`、`Free.v`；`Lambek.v`（结构箭≅）。笔记 `cabal run algebra-demos` 对照字段名。

## 4. 理论—模型—Monad 三角（原创串讲）

1. 签名→`L`；2. 保积模型；3. finitary `T`≈自由模型载体。细节见笔记 ①–⑧ 路径。

## 5. 易混 / 清单

Lawvere≠字面Monad；`law_of_nat` 用`=`；模型须保积；Free monad≠初始代数但相关。  
检查：Lawvere 字段；跑通 `law_pow_one`；Model.v；FAlg/Free 浏览；笔记 ①–③。



## 6. Lawvere：按笔记路径走读本库

笔记建议 ①定义与骨架 → ②模型 → ③幺半群理论 → ④finitary-monad …  

对本库：

| 笔记步 | 本库动作 |
|--------|----------|
| ① | 读完 `LawvereTheory`；跑 `law_pow_one` |
| ② | 打开 `Lawvere/Model.v`；找保积 |
| ③ | 搜 Monoid 相关理论/实例 |
| ④ | 打开 `Lawvere/Monad.v`；对照 `Theory/Monad` |
| ⑤ Maybe | 笔记文 + 可选 Instance |
| ⑥–⑧ | 以笔记为主；库中有则链路径 |

`Instance/FinSet/Lawvere.v`：看有限集骨架如何接 `law_of_nat`。

## 7. 初始代数 / Free：IDE 会话

1. `Construction/FAlg.v`：解释对象与 `FAlgHom`。  
2. `Theory/Lambek.v`：初始代数结构箭为同构——跟 Obligation。  
3. `Construction/Free.v`：自由函子/伴随字段。  
4. 笔记 `foldFree与cata.md`：用本库名字改写一句话对照。  
5. （可选）`Theory/Adamek.v`、`Recursion.v` 扫标题。

## 8. 严格 `=` vs `≈` 专题

`law_zero_terminal` / `law_plus_product` 用对象 `=`。这与全库态射层 `≈` 不同：

- 理论「骨架」选代表对象时，严格等式方便计算 `law_pow`；  
- 文献常写到同构为止；  
- 读模型文件时看保积是 `=` 还是 `≅`——两种都合理，混用会炸。

## 9. CoqIDE 检查清单（扩）

1. [ ] Lawvere 全字段。  
2. [ ] `law_pow_one` 逐步。  
3. [ ] Model.v 保积 Goal 形状。  
4. [ ] FinSet/Lawvere 浏览。  
5. [ ] FAlg + Lambek + Free 各打开。  
6. [ ] 笔记 ①–③ + Demo 横幅看过。  
7. [ ] 能默写「EM≠F-代数≠Lawvere 模型」一句。




## 10. 与 Monad 课的强制分线练习

写三段话（各≤3 句），禁止混用术语：

1. 只谈 `TAlgebra`（EM）；  
2. 只谈 `FAlg` / `cata`；  
3. 只谈 `LawvereTheory` / 模型。  

然后打开笔记对照表，看是否与「四层语言边界」一致。做完再继续 [12](12-instances.md)。


下一篇：[12 实例落地](12-instances.md)
