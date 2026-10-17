# 记号参考 (Notation reference)

`jwiegley/category-theory` 导出记号的一页参考。下列每一行都是 `Notation`（不是 `Reserved Notation`）；在对所述文件 `Require Import` 并打开正确 `Open Scope` 后可见。

## 命名约定

- 普通形式（`f ∘ g`、`x ~> y`、`x ≅ y`、…）用默认 scope。
- 消歧形式（`f ∘[C] g`、`x ~{C}~> y`、`x ⨂[M] y`、…）带显式范畴 / 幺半实例参数，在 Coq 类型类推断选不对实例时需要。
- 方括号形式（`obj[C]`、`id[x]`、`fobj[F]`、`mu[Mon]`）是投影 — 读作「具名结构的字段」。

## Scopes

库在 `Theory/Category.v` 中按下列顺序打开 scopes（后打开的优先）：

```coq
Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope morphism_scope.
```

`functor_type_scope` 与 `functor_scope` 由 `Theory/Functor.v` 打开。

| Scope                   | 由谁打开                  | 包含（代表）                       |
|-------------------------|----------------------------|-------------------------------------------------|
| `type_scope`            | Coq stdlib                 | `obj[C]`、`hom[C]`                              |
| `category_scope`        | `Theory/Category.v`        | `F ◯ G`（函子复合）                   |
| `homset_scope`          | `Theory/Category.v`        | `~>`、`~{C}~>`、`<~`、`<~{C}~`                  |
| `morphism_scope`        | `Theory/Category.v`        | `f ∘ g`、`f ∘[C] g`、`id[x]`、`id{C}`、`f ⁻¹`、`f ⨂ g`、`f ⨂[M] g`、`<$>`、`fmap[F]` |
| `category_theory_scope` | `Lib/Setoid.v`             | `f ≈ g`、`f ≈[C] g`                             |
| `object_scope`          | `Theory/Category.v`        | `x ⨂ y`、`x ⨂[M] y`、`fobj[F]`                  |
| `functor_type_scope`    | `Theory/Functor.v`         | `C ⟶ D`                                         |
| `functor_scope`         | `Theory/Functor.v`         | `(⨂)`、`Id[C]`                                  |
| `isomorphism_scope`     | `Theory/Isomorphism.v`     | `x ≅ y`、`x ≅[C] y`                             |
| `nat_scope`             | Coq stdlib                 | 数字 `0`、`1`、…、`+`                     |

注意：`f ⊙ g`（同构复合，`Theory/Isomorphism.v`）声明时没有 `: scope_name`，因此落在使用点当时打开的 scope。

## 核心态射 / 范畴记号

| 记号        | 定义                                                  | 源文件                |
|-----------------|-------------------------------------------------------------|----------------------------|
| `x ~> y`        | `@hom _ x y` — 推断范畴中的 hom 集             | `Theory/Category.v`        |
| `x ~{C}~> y`    | `@hom C x y` — 带显式范畴的 hom 集               | `Theory/Category.v`        |
| `x <~ y`        | `@hom _ y x` — 反向 hom               | `Theory/Category.v`        |
| `x <~{C}~ y`    | `@hom C y x` — 显式范畴的反向                   | `Theory/Category.v`        |
| `f ∘ g`         | 态射复合                                        | `Theory/Category.v`        |
| `f ∘[C] g`      | 显式范畴的复合                               | `Theory/Category.v`        |
| `f ≈ g`         | hom 集上的 setoid 等价（态射的通用「=」） | `Lib/Setoid.v` |
| `f ≈[C] g`      | 显式范畴的 setoid 等价                        | `Theory/Category.v`        |
| `id[x]`         | 对象 `x` 上的恒等态射                                    | `Theory/Category.v`        |
| `id{C}`         | `C` 中的恒等态射（对象推断）                  | `Theory/Category.v`        |
| `obj[C]`        | 范畴 `C` 的对象类型                                 | `Theory/Category.v`        |
| `hom[C]`        | 范畴 `C` 的 hom 集族                              | `Theory/Category.v`        |

**态射之间永远用 `≈`，绝不要用 `=`。** 本库基于 setoid；态射上的 `=` 是范畴错误（且过不了证明检查）。

## 同构 (Isomorphisms)

| 记号     | 定义                                          | 源文件              |
|--------------|-----------------------------------------------------|--------------------------|
| `x ≅ y`      | 推断范畴中的 `Isomorphism x y`          | `Theory/Isomorphism.v`   |
| `x ≅[C] y`   | `C` 中的 `Isomorphism x y`                            | `Theory/Isomorphism.v`   |
| `f ⁻¹`       | `from f` — 同构的逆                | `Theory/Isomorphism.v`   |
| `f ⊙ g`      | `iso_compose f g` — 同构的复合     | `Theory/Isomorphism.v`   |

## 函子与自然变换

| 记号       | 定义                                       | 源文件               |
|----------------|--------------------------------------------------|---------------------------|
| `C ⟶ D`        | `Functor C D`                                    | `Theory/Functor.v`        |
| `Id[C]`        | `C` 上的恒等函子                          | `Theory/Functor.v`        |
| `F ◯ G`        | 函子复合                              | `Theory/Functor.v`        |
| `fobj[F]`      | `F` 的对象作用                             | `Theory/Functor.v`        |
| `F ⟹ G`        | 自然变换 `F → G`                   | `Theory/Natural/Transformation.v` |
| `F ∙ G`        | 自然变换的垂直复合     | `Theory/Natural/Transformation.v` |
| `N ⊲ F`        | 右 whisker（后复合 `F`）              | `Theory/Natural/Transformation.v` |
| `F ⊳ N`        | 左 whisker（前复合 `F`）                | `Theory/Natural/Transformation.v` |

## 幺半 / 对称幺半

| 记号     | 定义                                                  | 源文件              |
|--------------|-------------------------------------------------------------|--------------------------|
| `x ⨂ y`      | 推断幺半中对象上的 `(tensor) (x, y)`           | `Structure/Monoidal.v`   |
| `x ⨂[M] y`   | 显式幺半 `(tensor M) (x, y)`                       | `Structure/Monoidal.v`   |
| `f ⨂ g`      | 经推断幺半的两态射 `bimap`              | `Structure/Monoidal.v`   |
| `f ⨂[M] g`   | 显式幺半 `bimap[tensor M] f g`                     | `Structure/Monoidal.v`   |
| `(⨂)`        | 张量双函子本身                                 | `Structure/Monoidal.v`   |
| `I`          | 幺半单位（从 `Monoidal` 实例投影）   | `Structure/Monoidal.v`   |
| `braid`      | 辫（来自 `BraidedMonoidal` 实例）            | `Structure/Monoidal/Braided.v` |

## 代数结构

| 记号         | 定义                            | 源文件                          |
|------------------|---------------------------------------|--------------------------------------|
| `mu[Mon]`        | 显式 `Monoid` 实例的 `μ`  | `Theory/Algebra/Monoid.v`            |
| `eta[Mon]`       | 显式 `Monoid` 实例的 `η`  | `Theory/Algebra/Monoid.v`            |
| `delta[Co]`      | 显式 `Comonoid` 实例的 `δ` | `Theory/Algebra/Comonoid.v`          |
| `epsilon[Co]`    | 显式 `Comonoid` 实例的 `ε` | `Theory/Algebra/Comonoid.v`          |

扁平投影 — 新代码优先：

  `scfa_mu`、`scfa_eta`、`scfa_delta`、`scfa_epsilon`
  （在 `Theory/Algebra/SpecialCommutativeFrobenius.v`）

  `cmon_mu`、`cmon_eta`
  （在 `Theory/Algebra/CommutativeMonoid.v`）

## PROP 记号

| 记号     | 定义                                                | 源文件              |
|--------------|-----------------------------------------------------------|--------------------------|
| `⟦n⟧`        | `prop_of_nat P n` — 元数 `n` 的 PROP 对象           | `Construction/PROP.v`    |

该记号绑定在 `Section PROPLemmas` 内（其中 `Context (P : PROP)`），经隐式 `P` 展开为 `@prop_of_nat P n`。在 section 外使用时，请用你的具体 `P` 本地重定义。

## 库基础符号（非 Notation）

| 符号       | 含义                                                |
|--------------|--------------------------------------------------------|
| `Setoid`     | Setoid 记录（载体 + 等价）                  |
| `Setoid_Theory` | setoid 性证明                                 |
| `Equivalence` | `Equivalence ≈` 是通用 homset 等价断言 |
| `Proper`     | 态射尊重逐点等价                |

声明 `Setoid` 的文件一经 Require，`Setoid` **自动打开**（无需额外 `Open Scope`）。

## 迁移说明：态射相等

若从在态射之间用 `=` 的项目迁过来，必须把每一处改成 `≈`。本库的 `Setoid` 实例使所有 `≈` rewrite 经标准 `setoid_rewrite` 通路工作，但 setoid-Coq 中态射上的 `=` 是范畴错误，会直接无法统一。没有自动翻译。
