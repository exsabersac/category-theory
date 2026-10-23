# 04 · 函子

**CTFP**：Ch.7 *Functors*，Ch.8 *Functoriality*。  
**DaoFP**：`8-Functors.tex`。  
**notes**：[haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)「函子组合」。

## 范畴论陈述

函子 = 对象映射 + 态射映射，保恒等与复合。本库另加 `fmap_respects`（setoid）。函子相等默认是自然同构意义下的（`Functor_Setoid`），不是对象逐点 `=`。

## 编程直觉

`fmap` / `<$>`；Maybe、List、Reader。双函子对应 `Bifunctor`。

## 路径与 Require

```coq
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Coq.Functor.   (* 仅 fmap 的程序类 *)
```

| 路径 | 作用 |
|------|------|
| `Theory/Functor.v` | `Class Functor`，`C ⟶ D` |
| `Functor/Bifunctor*` | 双函子 |
| `Functor/Hom*` | Hom 函子 |
| `Functor/Representable*` | 可表 |
| `Functor/Structure*` | 保结构的「种」 |
| `Theory/Coq/Functor.v` | 程序侧 EndoFunctor |

## 关键摘录

```coq
Class Functor {C : Category} {D : Category} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;
  fmap_respects : ∀ x y, Proper (respectful equiv equiv) (@fmap x y);
  fmap_id {x : C} : fmap (@id C x) ≈ id;
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
Notation "C ⟶ D" := (@Functor C%category D%category) ...
```

## CoqIDE 步骤

1. `Theory/Functor.v` → `Class Functor`，注意第三条定律 `fmap_respects`。
2. 搜 `Compose` / `Id` 实例，看函子范畴的预备。
3. 打开 `Functor/Hom.v`，为 Yoneda 篇铺路。
4. （可选）`Theory/Coq/Functor.v` 对比「只声明 fmap、定律经一般理论回收」。

下一篇：[05 自然变换](05-natural.md)
