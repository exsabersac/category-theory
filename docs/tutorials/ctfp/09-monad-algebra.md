# 09 · Monad、EM 代数与 F-代数（必须分清）

**CTFP**：1.4 *Kleisli Categories*；3.4 *Monads: Programmer's Definition*；3.5 *Monads and Effects*；3.6 *Monads Categorically*；3.8 *F-Algebras*；3.9 *Algebras for Monads*。  
**DaoFP**：`11-Algebras`、`13-Effects`、`14-Applicatives`（边界）、`15-Monads`、`16-MonadsAdjunctions`。

> 原创教学复述；不摘录书中正文。易混重灾区。

## 1. 书侧故事：三条线

1. **程序员**：`return`/`>>=`，效果顺序组合；Kleisli 箭头 `a -> M b` 先成范畴（CTFP 1.4）。  
2. **范畴**：自函子 + `η` + `μ` 单位结合；伴随导出 `U F`（CTFP 3.6 / DaoFP 16）。  
3. **代数**：  
   - **F-代数**：`α : F A ~> A`（任意自函子；初始 ⇒ `cata`）；  
   - **EM / T-代数**：对 **Monad** `T`，还要尊重 `η`、`μ`。

笔记必对读：[List的EM代数与Monoid](https://github.com/exsabersac/haskell-algebra-notes)、[docs/初始代数/](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/%E5%88%9D%E5%A7%8B%E4%BB%A3%E6%95%B0)、[docs/Free/](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/Free)。

DaoFP 13–15：效果列表；Applicative 并行 vs Monad 串行。

## 2. 本库 Monad：`Theory/Monad.v`

```coq
Class Monad := {
  ret {x} : x ~> M x;
  join {x} : M (M x) ~> M x;
  fmap_ret : ret ∘ f ≈ fmap f ∘ ret;
  join_fmap_join : join ∘ fmap join ≈ join ∘ join;
  join_fmap_ret  : join ∘ fmap ret ≈ id;
  join_ret       : join ∘ ret ≈ id;
  join_fmap_fmap : join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.
Definition bind f := join ∘ fmap[M] f.
```

## 3. EM：`Monad/Algebra.v`

```coq
Class TAlgebra `(T)` `{Monad} (a) := {
  t_alg : T a ~> a;
  t_id : t_alg ∘ ret ≈ id;
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
}.
```

同态：`t_alg_hom_commutes` 方块。

## 4. F-代数：`Construction/FAlg.v`

代数范畴（对象带 `F a ~> a`，态射交换方块）。**无** ret/join 义务。初始代数 / Lambek / cata：`Lambek.v`、`Adamek.v`、`Recursion.v`。

## 5. CoqIDE 证明走读

### 5.1 Monad 义务表

| 字段 | Goal | 直觉 |
|------|------|------|
| fmap_ret | η 自然方块 | |
| join_fmap_join | μ 结合 | List=concat 两序 |
| join_fmap_ret / join_ret | 左右单位 | |
| join_fmap_fmap | μ 自然 | |

### 5.2 `bind ret ≈ id`

```coq
Example bind_ret `{Monad C M} {x} : bind (@ret _ M x) ≈ id.
Proof. unfold bind. apply join_fmap_ret. Qed.
```

### 5.3 Kleisli 复合

鱼组合子精神：`f >=> g = join ∘ fmap g ∘ f`。结合律 ↔ `join_fmap_join`。打开 `Monad/` 下 Kleisli 文件（若有）看范畴实例义务。

### 5.4 T-代数与 Monoid

`mconcat : List A -> A`：`t_id`≈`mconcat [x]=x`；`t_action`≈先 concat 再折。对照笔记。

### 5.5 FAlg 范畴义务

`Program Definition FAlg`：id/compose 抬到代数同态；Obligation 多是方块 + `cat`。

## 6. 易混总表

| | F-代数 | EM 代数 |
|--|--------|---------|
| 对谁 | 任意 F | Monad T |
| 箭 | F A~>A | T A~>A |
| 额外定律 | 无（初始性另说） | 尊 ret/join |
| 例 | ListF→List | List→Monoid |
| 库 | FAlg.v | Monad/Algebra.v |

## 7. CoqIDE 检查清单

1. [ ] Monad 全字段；手证 bind ret。  
2. [ ] TAlgebra 两定律。  
3. [ ] FAlg 与 TAlgebra 三点不同。  
4. [ ] 笔记 EM vs 初始代数对照。  
5. [ ] （可选）Coq/Monad 实例。  
6. [ ] Applicative 文件名扫一眼（缺口）。



## 8. 更细的 CoqIDE 会话

### 会话 A：Monad 字段逐条 Check

```coq
Require Import Category.Theory.Monad.
(* 在已有 Monad 实例的上下文中 ）*)
Check @ret.
Check @join.
Check @bind.
```

对每个定律 `Check join_fmap_ret` 等，读类型，用中文说人话。

### 会话 B：List/option 实例（若有）

打开 `Instance/Coq/Monad.v` 或 Sets 侧 Monad：  
对 `join_ret` 把 `Proof. ... Qed` 暂时改成逐步，看 `simpl` 后 Goal 是否变成算式。

### 会话 C：TAlgebra 方块

打开 `Monad/Algebra.v`，解释 `t_alg_hom_commutes`。纸上画：

```text
T a --t_alg--> a
 | fmap hom     | hom
 v              v
T b --t_alg--> b
```

### 会话 D：FAlg 对比

打开 `Construction/FAlg.v` 的 `FAlgHom`：方块类似，但**没有** `t_id`/`t_action`。在笔记写一句：「少了这两条就是 F-代数同态」。

## 9. 书侧阅读顺序建议（避免混线）

1. CTFP 3.4–3.5（程序员 + 效果）或 DaoFP 13–15；  
2. CTFP 3.6 / DaoFP 16（η/μ 与伴随）；  
3. CTFP 3.8（F-代数）+ 笔记初始代数；  
4. CTFP 3.9（EM）+ 笔记 List-EM；  
5. 回本库对字段。  

不要同一天混着只读「代数」一词。


下一篇：[10 幺半、Kan、End](10-monoidal-kan-ends.md)
