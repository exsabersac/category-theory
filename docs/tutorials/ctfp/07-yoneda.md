# 07 · Yoneda

**CTFP**：Part Two Ch.4–6 *Representable Functors* / *The Yoneda Lemma* / *Yoneda Embedding*。

## 范畴论陈述

Yoneda：预层 `F : C^op ⟶ Sets` 在 `A` 处的值，同构于自然变换 `Hom(-,A) ⟹ F`。嵌入 `A ↦ Hom(-,A)` 全忠实。本库在 `Sets` 上陈述（setoid 版）。

## 编程直觉

「对象 = 它能被如何探测」；Continuation / 可表字典的范畴版。深挖与 optics 留作缺口。

## 路径与 Require

```coq
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Coend.Yoneda.
Require Import Category.Instance.Sets.
```

| 路径 | 作用 |
|------|------|
| `Functor/Hom.v`、`Hom/` | Hom 函子 |
| `Functor/Hom/Yoneda.v`、`Yoneda/` | 引理与嵌入 |
| `Theory/Universal/Element.v` | 泛元 |
| `Theory/Coend/Yoneda.v` | 余端视角 |
| `Functor/Representable.v` | 可表函子 |

## 关键摘录

```coq
Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) :
  ∀ A : C, Presheaves [Hom ─,A] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C^op }~> x =>
                     @fmap (C^op) Sets F A x phi y |} |} |}
}.
```

另有 `Covariant_Yoneda_Lemma`（共变版）。

## CoqIDE 步骤

1. 先会 `Functor/Hom.v` 的 Hom 函子。
2. `Functor/Hom/Yoneda.v`：解释 `Yoneda_Lemma`，逐义务看 `naturality` / `fmap_id`。
3. 打开 `Theory/Universal/Element.v`，对照「泛元」叙述。
4. （选读）`Theory/Coend/Yoneda.v`；Optics 方向见 notes，本系列暂不展开。

下一篇：[08 伴随](08-adjunction.md)
