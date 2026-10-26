# 05 · 自然变换

**CTFP**：1.10 *Natural Transformations*。  
**DaoFP**：`9-NaturalTransformations`（Hom 之间与一般函子之间；竖直/水平复合、whiskering、交换律；可表函子与 guessing game 引言）。

> 原创教学复述；不摘录书中正文。

## 1. 书侧故事：函子范畴的「箭头」

函子把范畴映到范畴；自然变换把平行函子映到「平滑的」一族态射。给定 `F, G : C ⟶ D`，自然变换 `η : F ⟹ G` 提供：

- 分量 `η_x : F x ~> G x`（每个对象一个）；  
- 自然性：对任意 `f : x ~> y`，`fmap[G] f ∘ η_x ≈ η_y ∘ fmap[F] f`。

CTFP 给程序员的口译是：参数多态的 `∀ x. F x -> G x`，自然性大致说「不偷看具体类型」。这不是形式定理（Hask 有坑），但是极好的导航直觉。

DaoFP 把自然变换放进更大的代数里：

- 竖直复合 → 函子范畴的态射复合；  
- 水平复合与 whiskering → 与函子复合的兼容；  
- 可表函子 → 为 Yoneda 做势。

本篇打方块与本库字段；[07](07-yoneda.md) 再用「Hom 上的自然变换 = 元素」。

## 2. 编程直觉

```haskell
-- safeHead :: forall a. [a] -> Maybe a
-- 自然性精神: fmap f . safeHead = safeHead . fmap f
```

反例直觉：`bad :: [Int] -> Maybe Int` 若先判断长度再决定是否偷看首元素类型信息，扩到多态时会破方块。形式检验仍看自然性 Goal。

## 3. 本库：`Theory/Natural/Transformation.v`

```coq
Class Transform := {
  transform {x} : F x ~> G x;

  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
}.
```

`Build_Transform'`：只交一个方向的自然性，另一方向 `symmetry` 自动填——**建变换时优先用**。

相等：`N0 ≈ N1` iff 点点分量 `≈`（`Transform_Setoid`）。

## 4. CoqIDE 证明走读

### 4.1 类体与 Build'

1. 打开文件，解释 `Transform`。  
2. 跟 `Build_Transform'` Proof：第二段 Goal 是 `_sym`，`symmetry; apply natural`。  
3. 看 `Transform_Setoid` 的 `equiv` 定义与 `Next Obligation`（`equivalence` 战术）。

### 4.2 在证明里使用自然性

假设 `η` 已是 `Transform`。Goal 含 `fmap[G] f ∘ transform ≈ ...`：

```coq
rewrite (naturality η f).  (* 或 naturality_sym，看朝向 *)
```

Yoneda 文件 Obligation 出现 `rewrite naturality; ...; cat`——可提前打开瞄一眼。

### 4.3 竖直复合走读

搜索竖直复合定义（名称可能含 `vcompose` / `compose` / `Native` 等，以源码为准）：

- 分量：`ε_x ∘ η_x`；  
- 自然性证明：两个方块上下粘，中间用 `compose_respects` 与各自 `naturality`。

逐步解释 Proof，在纸上画：

```text
F --η--> G --ε--> H
```

### 4.4 Whiskering（若存在）

`F ◃ η`：分量 `fmap[F] (η_x)` 或 `η` 后接 `F`——核对定义。Goal 自然性常化到 `fmap_comp`。找不到实现就记「概念保留」，不硬猜。

## 5. 书侧加厚：函子范畴

一旦自然变换可复合、有恒等（恒等变换分量 = `id`），`[C,D]` 成为范畴。CTFP / DaoFP 后文大量「对象是函子」的构造（Monad 是单子对象、Kan 在函子范畴里取值）都建于其上。本库用 `Transform` + 函子实例表达；大范畴 `Cat` 见 [12](12-instances.md)。

可表：`Hom(A,−) ⟹ F` 由 `F(A)` 的元素决定——下篇正式化。

## 6. 易混对比

| 说法 | 澄清 |
|------|------|
| 多态 ⇒ 自然 | 直觉；形式仍要方块 |
| 变换 = 一个态射 | 是一族 + 定律 |
| 只证一个方向 | 类要两向；用 `Build_Transform'` |
| 水平 vs 竖直 | 竖直同域同码串接；水平沿复合横向糊 |

## 7. CoqIDE 检查清单

1. [ ] 解释三字段。  
2. [ ] 跟完 `Build_Transform'`。  
3. [ ] 手写一次 `rewrite naturality`。  
4. [ ] 理解变换 setoid 相等。  
5. [ ] 扫竖直复合证明大纲。  
6. [ ] （可选）DaoFP Haskell 目录里 `9-Natural.hs` 等文件名对照概念。



## 8. 更细的 CoqIDE 会话记录（建议照做）

### 会话 A：从零看到第一个自然性 Goal

1. `coqide` 或 VsCoq 打开仓库根。  
2. 打开 `Theory/Natural/Transformation.v`，`Require` 链解释到无错。  
3. 光标停在 `Class Transform` 的结尾 `.` 上，确认三个字段进入环境。  
4. 找到任意 `Program Instance` 或 `Next Obligation` 含 `naturality` 的证明。  
5. 把光标放进 Proof 第一行，逐步：观察 Goal 是否形如  
   `fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f`。  
6. 若证明用 `cat`，先暂时改成手动：`rewrite fmap_comp` / `rewrite naturality` 等，看哪一步推进 Goal——再改回 `cat`。

### 会话 B：自建一个「恒等变换」

在 Scratch（记得 `-R . Category`）：

```coq
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.

Section IdNat.
  Context {C D : Category} (F : C ⟶ D).
  Program Definition id_transform : Transform F F := {|
    transform := fun _ => id
  |}.
  Next Obligation.
    (* naturality: fmap f ∘ id ≈ id ∘ fmap f *)
    rewrite id_left, id_right; reflexivity.
  Qed.
  Next Obligation.
    rewrite id_left, id_right; reflexivity.
  Qed.
End IdNat.
```

若 `Program` 只生成一个 Obligation，改用 `Build_Transform'`。成功后，你就独立交过自然性方块。

### 会话 C：点点相等

找两个应相等的变换（例如某复合的结合子），Goal `∀ x, transform A x ≈ transform B x`：先 `intros x`，再局部计算。不要对整个 `Transform` 用 Leibniz `=`。

## 9. 书侧概念对照表（CTFP 1.10 × DaoFP §9）

| 书中主题（标题级） | 本课落点 | 本库 |
|--------------------|----------|------|
| 分量 + 方块 | §1–3 | `transform`/`naturality` |
| 多态直觉 | §2 | 例子 `safeHead` |
| 竖直复合 | §4.3 | 源码复合 |
| 水平 / whiskering | §4.4 | 若有则扫 |
| 可表引言 | §5 | 接 [07](07-yoneda.md) |
| Hom 之间的变换 | 为 Yoneda | `Functor/Hom/*` |


下一篇：[06 极限](06-limits.md)
