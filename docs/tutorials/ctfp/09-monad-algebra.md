# 09 · Monad、Eilenberg–Moore 与 F-代数（勿混）

**CTFP**：Ch.4–6 *Monads…*，Ch.8–9 *F-Algebras* / *Algebras for Monads*。  
**DaoFP**：`15-Monads.tex`、`16-MonadsAdjunctions.tex`、`11-Algebras.tex`。  
**notes**：初始代数、Free。

## 范畴论陈述

- **Monad**：自函子 `M` + `ret`（η）+ `join`（μ）+ 定律；`bind` 可派生。
- **EM 代数**（`Monad/Algebra.v`）：`t_alg : M a ~> a` 与单位/结合律——这是单子上的代数。
- **F-代数**（`Construction/FAlg.v` 等）：对任意自函子 `F` 的 `F a ~> a`；初始 F-代数 ↔ Lambek；与 Adamek 构造相关。  
**两者不是同一 `Class`。** 读文件路径先分清。

Kleisli：`Monad/Kleisli.v`（CTFP Ch.4）。Comonad = 对偶（`Definition Comonad := Monad (C^op) ...`）。

## 编程直觉

`return`/`join`/`>>=`；`State`/`Maybe`。EM 代数 ≈「能解释这个效应的载体」。初始 F-代数 ≈ 归纳类型（notes「初始代数」）。

## 路径与 Require

```coq
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.       (* EM：TAlgebra *)
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Adjunction.    (* 伴随 ↔ 单子 *)
Require Import Category.Construction.FAlg.   (* F-代数，另一路 *)
Require Import Category.Theory.Lambek.
Require Import Category.Theory.Adamek.
```

## 关键摘录

```coq
(* Theory/Monad.v *)
Class Monad := {
  ret {x}  : x ~> M x;
  join {x} : M (M x) ~> M x;
  fmap_ret ... ; join_fmap_join ... ;
  join_fmap_ret ... ; join_ret ... ; join_fmap_fmap ...
}.
Definition bind {x y} (f : x ~> M y) : M x ~> M y := join ∘ fmap[M] f.

(* Monad/Algebra.v — EM *)
Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  t_alg : T a ~> a;
  t_id     : t_alg ∘ ret ≈ id;
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
}.
```

F-代数见 `Construction/FAlg.v` 的 `FAlgHom` 等——证明目标与 `TAlgebra` 不同。

## CoqIDE 步骤

1. `Theory/Monad.v` 全文很短：解释完 `Monad` 与 `bind`。
2. `Monad/Kleisli.v`：看 `>=>` 与 CTFP Kleisli 章对应。
3. `Monad/Algebra.v`：EM 两定律。
4. **另开** `Construction/FAlg.v` + `Theory/Lambek.v`，在笔记里写一句「这不是 TAlgebra」。
5. （选）`Monad/Adjunction.v`、`Theory/Adamek.v`；Comonad 目录留作缺口加厚。

下一篇：[10 幺半 · Kan · End](10-monoidal-kan-ends.md)
