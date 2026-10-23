# 05 · 自然变换

**CTFP**：约 1.10（自然变换章）。  
**DaoFP**：`9-NaturalTransformations` 一带（同章后文常接极限）。

## 这个概念在干什么

自然变换是**函子之间的态射**：对每个对象给一个分量箭头，且这些分量必须与两个函子的 `fmap` **交换**——这就是自然性方块。

历史上，范畴论就是为了把「自然的同构」说清楚才发明的。双重对偶 `V → V**` 自然，而 `V → V*` 在选基底前不自然：逐点有同构，却拼不成与所有线性映射交换的一族。

## 短例子

```haskell
-- 候选：对每个 a，一条 F a -> G a
headMay :: [a] -> Maybe a   -- 这是自然的（多态 + 不偷看 a 的构造）

-- 自然性（直觉）：
-- fmap g . η = η . fmap g
```

程序员口诀：**参数多态的 `F a → G a`（且实现不 cheat）≈ 自然变换分量**。自由定理往往保证自然性；在本库你要**证明** `naturality`。

## 本库：`Theory/Natural/Transformation.v`

```coq
Class Transform := {
  transform {x} : F x ~> G x;

  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
}.
```

上下文是 `F G : C ⟶ D`。记号上常把 `Transform` 实例看成 `F ⟹ G`。

### 字段怎么读

- `transform`：在每个对象 `x` 上的分量 `η_x : F x ~> G x`；
- `naturality`：方块 `G f ∘ η_x ≈ η_y ∘ F f`；
- `naturality_sym`：同一等式翻面——又是为了对偶/重写方便的刻意冗余；`Build_Transform'` 只让你证一个方向。

`Transform_Setoid`：两个自然变换相等，当且仅当**每个分量** `≈`。

### 典型 Goal

证自然性时 Goal 多是：

```text
fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f
```

策略常是：展开 `F`/`G` 的 `fmap` 定义，用它们的 `fmap_comp` / `fmap_id`，再 `cat` 或 setoid rewrite。  
若 `F`、`G` 来自复杂构造，先 `destruct F` / 简化到 `fmap` 字段。

## 复合方式（同目录后续）

自然变换不止「分量」：

- **垂直复合**：`F⟹G` 与 `G⟹H` 合成 `F⟹H`（分量合成）；
- **水平 / whiskering / Godement**：与函子复合交互。

读完本文件的 `Transform` 后，再在同目录浏览复合定义，才能看懂「函子范畴的态射合成」以及伴随里单位/余单位作为自然变换的身份。

## 和 Yoneda、伴随的接口

- Yoneda：`Hom(A,–)` 到 `F` 的自然变换 ↔ `F A` 的元（见 [07](07-yoneda.md)）；
- 伴随的 hom-集形式：一族**在两边都自然**的同构（见 [08](08-adjunction.md)）；
- Monad 的 `ret`/`join`：其实是自然变换，本库在 `Monad` 类里用 `fmap_ret`、`join_fmap_fmap` 把自然性方块展开成定律。

## 易混对比

| 易混 | 分清 |
|------|------|
| 每个对象有个 `F x ~> G x` | 只是**分量族**；缺自然性就不是自然变换 |
| 自然同构 vs 自然变换 | 前者每个分量还是同构（可逆且逆也自然，或等价条件） |
| 「多态故自然」 | 在 Coq/本库必须交证明；别默认 |
| dinatural / extranatural | 双变元、End/Coend 用；见 [10](10-monoidal-kan-ends.md)，比本篇多 |

## CoqIDE 步骤

1. 打开 `Theory/Natural/Transformation.v`，解释 `Class Transform`。
2. 看 `Build_Transform'`：如何从单方向自然性生成 `naturality_sym`。
3. 打开 `Instance/Fun.v`（或 `[C,D]` 相关），确认「态射 = 自然变换、相等 = 分量点点 ≈」。
4. 任挑一个具体自然变换实例（例如与 `Id`、嵌入相关），观察 `naturality` 的 Obligation 证明长什么样。
5. 在 `Theory/Monad.v` 里对照 `fmap_ret`——确认它就是 η 的自然性方块。


## 自然性方块怎么画（读证明前先画）

固定 `f : x ~> y`：

```text
F x --η_x--> G x
 |            |
F f          G f
 v            v
F y --η_y--> G y
```

要证两条路径 `≈`：`G f ∘ η_x` 与 `η_y ∘ F f`。  
`naturality` 字段取前者 ≈ 后者；`naturality_sym` 反过来——重写方向不够时换用。

### 垂直复合（你接下来会用到）

若 `σ : F⟹G`、`τ : G⟹H`，分量：

```text
(τ • σ)_x  :=  τ_x ∘ σ_x
```

自然性：把两个方块上下叠，用 `comp_assoc` 粘合。函子范畴的态射复合就是这个。

Whiskering（侧面长出毛）：函子 `H` 事后/事前复合，分量变成 `fmap[H] (σ_x)` 或 `σ_(K x)`。Godement 积把两侧合在一起——名称在同目录后续文件；读伴随单位「是自然变换」时会碰到。

### 反例直觉（为什么不能只给分量）

对每个向量空间选一组基，得到 `V ≅ V*` 的「同构族」，但换基后与线性映射不交换——**没有自然性**。  
双重对偶 `V → V**` 才有规范、自然的族。这个故事是发明「自然变换」一词的动机；读 `Transformation.v` 文首中文导言可对照。

下一篇：[06 锥与极限](06-limits.md)
