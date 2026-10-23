# 04 · 函子

**CTFP**：1.7 *Functors*；1.8 *Functoriality*。  
**DaoFP**：`8-Functors`（先回顾范畴种类：Sets、对偶、积范畴、切片/余切片；再函子、自函子、双函子；编程 fmap）。

> 原创教学复述；不摘录书中正文。

## 1. 书侧故事：把「结构」搬到另一范畴

范畴论的「态射」不只存在于对象之间——范畴与范畴之间也有态射，叫 **函子**。一对映射：

- 对象：`fobj : C → D`；  
- 态射：`fmap : (x ~> y) → (F x ~> F y)`；  

并满足：

- `fmap id ≈ id`；  
- `fmap (f ∘ g) ≈ fmap f ∘ fmap g`。

CTFP 强调定律不可省略：随便写个 `map` 若弄破恒等或复合，就不是函子。*Functoriality* 继续问：积、余积、指数、复合类型何时**自动**获得 `fmap`（双函子、协变/反变位置）。

DaoFP 的路径更「先建世界再谈映射」：先让你熟悉对偶、积范畴、切片，再定义函子——因为许多例子天然是 `C^op ⟶ D` 或 `C × D ⟶ E`。

你的笔记 [docs/函子组合/](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/%E5%87%BD%E5%AD%90%E7%BB%84%E5%90%88) 把函子当可叠积木；本库用函子复合实例对应这件事。

## 2. 编程直觉

```haskell
fmap id = id
fmap (f . g) = fmap f . fmap g
```

| 例子 | 方差 | 范畴论说法 |
|------|------|------------|
| `List`/`Maybe` | 协变 | `C ⟶ C` 自函子 |
| `Predicate a = a -> Bool` | 对 `a` 反变 | `C^op ⟶ Set`（精神） |
| `Either e` / `(,) e` | 对右侧协变 | 固定一变元的双函子 |
| `a -> b` | 对 `b` 协变、对 `a` 反变 | Hom 函子 |

本库不单独建 `Contravariant` 类也能表达反变：走 `Opposite`。

## 3. 本库：`Theory/Functor.v`

```coq
Class Functor {C D : Category} := {
  fobj : C → D;
  fmap {x y} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects : ∀ x y, Proper (equiv ==> equiv) (@fmap x y);
  fmap_id {x} : fmap (@id C x) ≈ id;
  fmap_comp {x y z} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
```

记号：`C ⟶ D`；`fmap` 亦可 `<$>`。`Coercion fobj`：函子可当对象函数用。

相关：

- `Full` / `Faithful`：满 / 忠实；  
- `AFunctor`：先给对象映射再补全；  
- 恒等函子、复合函子实例（同文件后部）；  
- `Theory/Coq/Functor.v`：编程向。

## 4. CoqIDE 证明走读

### 4.1 解释类体

打开 `Theory/Functor.v`，跳到 `Class Functor`，逐步解释。确认 `Existing Instance fmap_respects`（或等价导出）已执行，否则 `rewrite` 在 `fmap` 下可能失败。

### 4.2 手写重写

```coq
Section FmapWalk.
  Context `{Functor C D} {x : C} {y : D} (h : fobj x ~> y).
  Example ex : h ∘ fmap id ≈ h.
  Proof.
    rewrite fmap_id.   (* Goal: h ∘ id ≈ h *)
    rewrite id_right.
    reflexivity.
  Qed.
End FmapWalk.
```

再试 `cat` 一键版，对比。

### 4.3 复合函子的 `fmap_comp`

设 `G ◯ F`，`fmap` 定义为 `fmap[G] (fmap[F] f)`。Goal：

```text
fmap[G] (fmap[F] (f ∘ g))
  ≈ fmap[G] (fmap[F] f) ∘ fmap[G] (fmap[F] g)
```

步骤：

1. `rewrite (fmap_comp (f:=f) (g:=g) (Functor0:=F))` 得内层拆开；  
2. `rewrite (fmap_comp (Functor0:=G))`；  
3. `cat` 或 `reflexivity`。

**练习**：在 IDE 里对抽象 `F`/`G` 写 `Example`，不要打开具体实例。

### 4.4 建实例时的 Obligation

`Program Instance` 某函子常见三类义务：

1. `Proper` → `proper`；  
2. `fmap_id` → 计算 / `reflexivity`；  
3. `fmap_comp` → 计算或用已有引理。

Sets 上容器实例：义务常变成函数级等式；看 `Instance/` 如何 `simpl`。

### 4.5 Full / Faithful

```coq
Class Full `(F : C ⟶ D) := { ... }.      (* 对态射「满」 *)
Class Faithful `(F : C ⟶ D) := { ... }. (* 对态射「单」 *)
```

Yoneda 嵌入满忠实——预告 [07](07-yoneda.md)。现在只需读定义字段。

## 5. 书侧加厚：Functoriality 检查清单

读 CTFP 1.8 / DaoFP 双函子节时，可用这张表自问（原创）：

| 构造 | 问 | 本库去哪验证 |
|------|----|--------------|
| 积 `×` | 是否双函子？ | `Cartesian` 的 `first`/`second`/`split` |
| 指数 | 方差？ | `Closed` 后续引理 |
| 复合 `G∘F` | 是否函子？ | `Functor` 复合实例 |
| 对偶 | `F^op`？ | `Opposite` + 函子 |

## 6. 易混对比

| 说法 | 澄清 |
|------|------|
| 有 map 就有函子 | 缺定律则否 |
| 自函子 = Monad | Monad 是自函子 + η/μ |
| 满忠实 = 等价 | 还缺本质满 |
| `fmap_respects` 烦 | E-category 必需 |

## 7. CoqIDE 检查清单

1. [ ] 解释五字段。  
2. [ ] 手写 `rewrite fmap_id`。  
3. [ ] 抽像证明复合函子的 `fmap_comp`。  
4. [ ] 找到 Id 与复合实例。  
5. [ ] 扫 Full/Faithful。  
6. [ ] 笔记「函子组合」对照 10 分钟。  
7. [ ] （可选）`Theory/Coq/Functor.v`。

下一篇：[05 自然变换](05-natural.md)
