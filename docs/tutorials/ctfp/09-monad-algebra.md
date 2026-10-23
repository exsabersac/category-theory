# 09 · Monad、Eilenberg–Moore 代数与 F-代数（必须分清）

**CTFP**：Kleisli / Monads / F-Algebras / Algebras for Monads（约 3.4–3.6、3.8–3.9）。  
**DaoFP**：`11-Algebras`、`15-Monads`、`16-MonadsAdjunctions`。  
**笔记**：[初始代数](https://github.com/exsabersac/haskell-algebra-notes)、[Free](https://github.com/exsabersac/haskell-algebra-notes)、[幺半范畴](https://github.com/exsabersac/haskell-algebra-notes)（List 的 EM 代数 ↔ Monoid）。

## 先钉死易混点

| 名称 | 本库 | 吃什么 | 典型用途 |
|------|------|--------|----------|
| **Monad** | `Theory/Monad.v` | 自函子 `M` + `ret`/`join` | 效应、`>>=` |
| **EM 代数 / T-代数** | `Monad/Algebra.v` → `TAlgebra` | **已经是 Monad 的** `T` | 「如何消解效应」；List 的 EM ≈ Monoid |
| **F-代数** | `Construction/FAlg.v` 等 | **任意**自函子 `F` 的 `F a ~> a` | 初始代数、`cata`、归纳类型 |
| **Monoid 对象** | `Theory/Algebra/Monoid.v` 等 | 幺半范畴里的对象 | 「Monad = End 里的 monoid」 |

**`TAlgebra` 不是 `FAlgebra`。** 路径不同、定律不同、证明目标不同。CTFP 两章挨着，最容易混。

## Monad：机制与本库

自函子 `M : C ⟶ C` 加上：

- `ret`（η）：`x ~> M x`；
- `join`（μ）：`M (M x) ~> M x`；

满足结合与两条单位，并把 η、μ 的自然性写成显式定律。

```coq
Class Monad := {
  ret {x}  : x ~> M x;
  join {x} : M (M x) ~> M x;

  fmap_ret {x y} (f : x ~> y) : ret ∘ f ≈ fmap f ∘ ret;           (* η 自然 *)
  join_fmap_join {x} : join ∘ fmap join ≈ join ∘ join;            (* 结合 *)
  join_fmap_ret  {x} : join ∘ fmap ret ≈ id;                      (* 左单位 *)
  join_ret       {x} : join ∘ ret ≈ id;                           (* 右单位 *)
  join_fmap_fmap {x y} (f : x ~> y) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join                         (* μ 自然 *)
}.

Definition bind {x y} (f : x ~> M y) : M x ~> M y := join ∘ fmap[M] f.
```

`bind` / `>>=` 是派生；Haskell 以 bind 为原始、join 为派生——逻辑等价，本库选 join/return 呈现。

等价观点：Monad = 自函子范畴 `[C,C]`（复合为张量）里的 **monoid 对象**（`Monad/Monoid.v`）。

### 编程直觉

```haskell
return :: a -> m a
join   :: m (m a) -> m a
(>>=)  :: m a -> (a -> m b) -> m b
```

`Maybe`、`State`、`IO`… 都是「带效应的值」的包装 + 合法压平方式。

### Kleisli：`Monad/Kleisli.v`

对象仍是 `C` 的对象，态射改成 `x ~> M y`，复合用 `>=>`（Kleisli 复合）。CTFP 很早讲 Kleisli：先有「箭头进 Monad」的范畴，再抽象出 Monad 定律。

## EM 代数：`Monad/Algebra.v`

```coq
Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  t_alg : T a ~> a;
  t_id     : t_alg ∘ ret ≈ id;                       (* 消掉纯值 *)
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join     (* 两次作用 = 先 join 再作用 *)
}.
```

直觉：`t_alg` 是「把效应层折进载体 `a`」的合法折叠。  
例：`T = List` 时，EM 代数结构 ≈ `a` 上的 monoid（`mconcat` 类东西）——笔记「List 的 EM 代数与 Monoid」讲的就是这条桥。

`TAlgebraHom`：在底层箭头上交换 `t_alg` 的方块。所有 EM 代数拼成 Eilenberg–Moore 范畴，见 `Monad/Eilenberg/Moore/`；遗忘函子有左伴随（自由代数 `(T a, join)`）。

## F-代数：另一条路

对任意自函子 `F`（**不要求 Monad**）：

```text
α : F a ~> a
```

叫 F-代数。`Construction/FAlg.v` 把它们做成范畴：态射是交换方块

```text
f ∘ α ≈ β ∘ fmap f
```

（类名 `FAlgHom`）。

**初始 F-代数** `(μF, in)`：从它到任意 F-代数有唯一代数同态——这就是 **`cata`（catamorphism）**。Lambek 定理：`in` 是同构。Adamek 构造：用迭代逼近初始代数（`Theory/Adamek.v`、`Theory/Lambek.v`、`Theory/Recursion.v`）。

编程：归纳类型 ≈ 某函子的初始代数；`fold`/`cata` ≈ 初始性给出的唯一箭头。见笔记「初始代数」「Free」。

### Free 与 Monad 的衔接（预告 [11]）

`Free F` 常构造为某初始代数 / 自由 Monad；EM 与 Free–Forgetful 伴随又回到 [08](08-adjunction.md)。先分清表，再串故事。

## Comonad

文件末尾：`Definition Comonad := Monad (C^op) …` 一类对偶。字段变成 `extract` / `duplicate` 味。本系列不单开深挖；目录 `Comonad/` 可自行对照。

## 易混对比（再练一次）

| 场景 | 用哪一个 |
|------|----------|
| `>>=`、效应顺序 | `Monad` |
| 「List 上的 monoid 结构」 | `TAlgebra`（EM） |
| `data Expr = …` + `cata` | `FAlgebra` / `FAlg` + 初始性 |
| 「Monad 是 End 的 monoid」 | monoid 对象，不是 EM，也不是 F-代数 |

## CoqIDE 步骤

1. 打开 `Theory/Monad.v`，解释完整个 `Class Monad` 与 `bind`（文件很短，适合精读）。
2. 打开 `Monad/Kleisli.v`，找到 Kleisli 复合与单位，对照 CTFP Kleisli 章的形状。
3. 打开 `Monad/Algebra.v`，只读 `TAlgebra` / `TAlgebraHom` 两定律。
4. **另开窗口** `Construction/FAlg.v`：读 `FAlgHom` 与 `FAlg` 范畴定义；在笔记本写一句「不是 TAlgebra」。
5. 打开 `Theory/Lambek.v` 看定理陈述（不必跟完所有证明）。
6. （选）`Monad/Adjunction.v`：伴随 ↔ 单子；`Theory/Adamek.v`：初始代数构造。

## 相关笔记

- [初始代数](https://github.com/exsabersac/haskell-algebra-notes)  
- [Free](https://github.com/exsabersac/haskell-algebra-notes)  
- [幺半范畴](https://github.com/exsabersac/haskell-algebra-notes)（EM↔Monoid）

下一篇：[10 幺半 · Kan · End](10-monoidal-kan-ends.md)
