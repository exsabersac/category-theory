# 01 · 范畴与态射

**CTFP**：Part One Ch.1 *Category: The Essence of Composition*，Ch.2–3 *Types and Functions* / *Categories Great and Small*。  
**DaoFP**：`2-Composition.tex`、`3-Isomorphism.tex`。

## 范畴论陈述

范畴 = 对象 + 态射 + 恒等 + 结合的复合。对象「是什么」不重要；性质全经出入态射表述。本库实现的是 **E-category**：每个 hom 是 setoid，相等是 `≈`，复合必须 `Proper`。

## 编程直觉

Haskell 里函数复合 `(.)` 与 `id`；这里换成任意 `hom`，定律写成 typeclass 字段。

## 路径与 Require

```coq
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.   (* C^op *)
(* 程序向子库： *)
Require Import Category.Theory.Coq.
```

| 文件 | 作用 |
|------|------|
| `Theory/Category.v` | `Class Category` |
| `Theory/Isomorphism.v` | `≅`、`⁻¹` |
| `Theory/Morphisms.v` | mono/epi 等 |
| `Construction/Opposite.v` | 对偶范畴 |
| `Theory/Coq.v` 及子目录 | Gallina/程序侧入口 |

## 关键摘录

```coq
Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};
  hom : obj → obj → uhom where "a ~> b" := (hom a b);
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);
  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);
  compose_respects {x y z} : Proper ... (@compose x y z);
  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;
  comp_assoc ... : f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;
  comp_assoc_sym ... : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.
```

`comp_assoc_sym` 是刻意冗余，让 `C^op^op` 对 `C` 可由 reflexivity 收回。

## CoqIDE 步骤

1. 打开 `Theory/Category.v`，跳过文首长注释，停在 `Class Category`。
2. 逐步解释到 `End`/`Existing Instance`；Goal 里看清 `≈` 来自 `homset`。
3. 打开 `Theory/Isomorphism.v`，找到 `Class Isomorphism` 与记号 `≅`。
4. 打开 `Construction/Opposite.v`，确认对偶如何交换 `comp_assoc` / `comp_assoc_sym`。
5. （可选）`Theory/Coq.v` 扫一眼程序子库入口，细节留到 Instance 篇。

下一篇：[02 积与和](02-products.md)
