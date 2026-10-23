# 05 · 自然变换

**CTFP**：Ch.10 *Natural Transformations*。  
**DaoFP**：`9-NaturalTransformations.tex`。

## 范畴论陈述

自然变换 `η : F ⟹ G` 给每个对象分量 `η_x : F x ~> G x`，且对任意 `f` 自然性方块交换。本库类名是 `Transform`，并带 `naturality_sym`（对偶友好）。

## 编程直觉

「多态函数且 free theorem 保证自然」——在任意范畴上没有 parametricity，必须手写 `naturality`。

## 路径与 Require

```coq
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Naturality.     (* 相关引理/工具 *)
```

| 文件 | 作用 |
|------|------|
| `Theory/Natural/Transformation.v` | `Class Transform`，`⟹`，whiskering |
| `Theory/Naturality.v` | 自然性辅助 |
| `Natural/Transformation/` | 变种与构造 |

## 关键摘录

```coq
Class Transform := {
  transform {x} : F x ~> G x;
  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;
  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
}.
Notation "F ⟹ G" := (@Transform _ _ F%functor G%functor) ...
```

复合：`∙`；whisker：`⊲` / `⊳`。

## CoqIDE 步骤

1. 打开 `Theory/Natural/Transformation.v`，解释 `Class Transform`。
2. 用 `Build_Transform'` 看如何只证一个方向的自然性。
3. 向下到 `nat_compose`、whisker，不必一次证完。
4. 回想 CTFP：自然变换是「函子之间的态射」→ 下一层是函子范畴 / Yoneda。

下一篇：[06 极限](06-limits.md)
