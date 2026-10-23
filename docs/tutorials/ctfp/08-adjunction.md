# 08 · 伴随

**CTFP**：Part Three Ch.2 *Adjunctions*，Ch.3 *Free/Forgetful Adjunctions*。  
**DaoFP**：`10-Adjunctions.tex`。

## 范畴论陈述

`F ⊣ U`：自然同构 `C(F x, y) ≅ D(x, U y)`（本库经 `Sets` 上的 `Isomorphism`），或等价地 unit η / counit ε + 三角。自由-遗忘是样板。

## 编程直觉

`Free ⊣ Forget`：List 作自由幺半；curry 作 `(- × a) ⊣ (a ⟹ -)`。

## 路径与 Require

```coq
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Hom.       (* 等变种，按需 *)
Require Import Category.Instance.Sets.
```

浏览 `Adjunction/`：`Compose`、`FullFaithful`、`Diagonal`、`GAFT`/`SAFT`、`Continuity` 等。

## 关键摘录

```coq
Class Adjunction := {
  adj {x y} :
    @Isomorphism Sets
      {| carrier := @hom C (F x) y; ... |}
      {| carrier := @hom D x (U y); ... |}
    where "⌊ f ⌋" := (to adj f) and "⌈ f ⌉" := (from adj f);
  to_adj_nat_l ... : ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  to_adj_nat_r ... : ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;
  from_adj_nat_l ... ;
  from_adj_nat_r ...
}.
Definition unit   {x : D} : x ~> U (F x) := ⌊id⌋.  (* η *)
Definition counit {x : C} : F (U x) ~> x := ⌈id⌉.  (* ε *)
Notation "F ⊣ G" := (@Adjunction _ _ F G) ...
```

## CoqIDE 步骤

1. `Theory/Adjunction.v` → `Class Adjunction`，盯住 `adj` 的两边是 **Sets 中的同构**。
2. 解释到 `unit`/`counit` 与三角相关 corollary。
3. 扫 `Adjunction/README.md`（若有）选下一条阅读线（连续性 / GAFT 等）。
4. 为 Monad 篇预习：伴随诱导单子 `U F`。

下一篇：[09 Monad 与代数](09-monad-algebra.md)
