# 02 · 第一个证明游走：Category → Functor → Transform

打开三个文件，按字段读一遍。目标不是证完所有引理，而是认路。

建议在 IDE 里依次打开：

1. `Theory/Category.v`
2. `Theory/Functor.v`
3. `Theory/Natural/Transformation.v`

并保证已 `Require Import Category.Lib`（它们自己会写）。

## 1. 范畴：`Theory/Category.v`

核心是类型类 `Category`（宇宙参数 `o h p`，且 `h <= p`）：

```coq
Class Category@{o h p | h <= p} : Type@{…} := {
  obj : Type@{o};
  hom : obj → obj → …    where "a ~> b" := (hom a b);
  homset : ∀ X Y, Setoid (X ~> Y);   (* 相等是 ≈ *)
  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);
  compose_respects : …;             (* 复合尊重 ≈ *)
  id_left  … ; id_right … ;
  comp_assoc … ;
  comp_assoc_sym …                  (* 镜像形式，方便对偶 *)
}.
```

读法：

- **对象**是 `obj`；**态射**是 `hom`，写作 `a ~> b`。
- 态射相等来自 `homset` 上的 setoid，写作 **`≈`**。证明里对态射做 `rewrite` 走的是 setoid rewriting。
- `comp_assoc` 与 `comp_assoc_sym` 成对出现，是为了让 `C^op^op` 对 Coq 化简后就是 `C`（见 `Construction/Opposite.v` 与 README「对偶」节）。

常用记号（完整表见 `docs/NOTATION.md`）：

- `obj[C]`、`hom[C]`、`id[x]`、`f ∘ g`
- `X ~{C}~> Y`：显式写出范畴，帮类型推断

自己写证明时，库提供 `Lib/Tactics.v` 里的 `cat`、`proper` 等；先 `Search` / 看上下文，再考虑上 tactic。

## 2. 函子：`Theory/Functor.v`

```coq
Class Functor {C : Category} {D : Category} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;
  fmap_respects : …;                 (* 尊重 ≈ *)
  fmap_id   : fmap id ≈ id;
  fmap_comp : fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
```

记号：`C ⟶ D` 表示 `@Functor C D`。`fobj` 有 coercion，常把函子当「作用在对象上的函数」写。

复合与恒等函子也在本文件（`Compose`、`Id`）；函子之间的「相等」按设计是自然同构意义下的 setoid（`Functor_Setoid`），不是对象映射的逐点 `=`。这影响你在 `Cat` 里谈态射相等时的直觉——见 [05](05-instances.md)。

短例子（示意，具体实例在 `Instance/`）：

```coq
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

(* 类型：函子是 Category → Category 上的结构 *)
Check @Functor.
(* 记号 C ⟶ D *)
```

## 3. 自然变换：`Theory/Natural/Transformation.v`

在固定 `F, G : C ⟶ D` 下：

```coq
Class Transform := {
  transform {x} : F x ~> G x;
  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;
  naturality_sym …                  (* 同样为对偶准备 *)
}.
```

记号：`F ⟹ G` 表示该 `Transform`。分量可经 coercion 当「在每个对象上的态射」用。

垂直复合、whiskering 等在同文件后续；需要时再往下翻，先把「一族分量 + 自然性方块」钉住即可。

## 4. 推荐的 Require 写法

日常起步：

```coq
Require Import Category.Theory.
(* 等价于导出 Category、Isomorphism、Functor、
   Natural.Transformation、Adjunction，以及若干 Structure *)
```

若只想最小依赖：

```coq
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
```

## 5. 你在 IDE 里可以做的三分钟练习

1. 打开 `Theory/Category.v`，跳到 `Class Category`，对 `id_left` 做一次 Search / 看谁在用。
2. 打开 `Theory/Functor.v`，确认 `fmap_id` / `fmap_comp` 的类型里已经是 `≈`。
3. 打开 `Natural/Transformation.v`，对照注释里的方块：`G f ∘ η_x ≈ η_y ∘ F f`。

下一篇：[03 常用结构](03-structures.md)
