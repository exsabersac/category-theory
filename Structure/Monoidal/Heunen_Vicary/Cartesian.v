Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Semicartesian.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Proofs.

Generalizable All Variables.

(** The cartesian-monoidal tensor is the categorical product. / 笛卡尔-单体张量是范畴积。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 This is the "Fox's theorem" direction made concrete: a symmetric monoidal
 category equipped with a natural diagonal ∆ (RelevanceMonoidal, copying)
 and a terminal unit / augmentation `eliminate` (SemicartesianMonoidal,
 discarding), subject to the counit laws proj_*_diagonal, has its tensor
 x ⨂ y serve as the categorical product x × y.  Fox 1976, "Coalgebras and
 cartesian categories", Comm. Algebra 4(7):665-667.

 The construction reads off a [Cartesian] structure on C from the
 CartesianMonoidal data, transporting along

 product_obj x y := x ⨂ y      (tensor is the product object)
 fork f g        := (f ⨂ g) ∘ ∆ (the pairing ⟨f, g⟩, from Relevance)
 exl             := proj_left   = unit_right ∘ id ⨂ eliminate
 exr             := proj_right   = unit_left  ∘ eliminate ⨂ id

 The single obligation discharges the universal mapping property
 ump_products, h ≈ ⟨f, g⟩ ↔ exl ∘ h ≈ f ∧ exr ∘ h ≈ g, from projection
 naturality (proj_*_natural), the counit laws (proj_*_diagonal) and the
 fork/projection round-trip proj_left_right_diagonal.  The closing coercion
 then lets every CartesianMonoidal category be used as a Cartesian one. 

 --------
 nLab：https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia：https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 这是“Fox 定理”方向的具体实现：一个对称幺半范畴配备了自然对角 ∆（RelevanceMonoidal，复制）和终端单位/增广 `eliminate`（SemicartesianMonoidal，丢弃），并满足余单位律 proj_*_diagonal，其张量 x ⨂ y 作为范畴积 x × y。Fox 1976，“Coalgebras and cartesian categories”，Comm. Algebra 4(7)：665-667。

 该构造从 CartesianMonoidal 数据中读取 C 上的 [Cartesian] 结构，并沿着传输product_obj x y := x ⨂ y （张量是乘积对象）
 fork f g := (f ⨂ g) ∘ ∆ （成对 ⟨f, g⟩，来自相关性）
 exl := proj_left = unit_right ∘ id ⨂ eliminate
 exr := proj_right = unit_left ∘ eliminate ⨂ id

 单一的义务完成了乘积的普遍映射性质
 ump_products, h ≈ ⟨f, g⟩ ↔ exl ∘ h ≈ f ∧ exr ∘ h ≈ g，来自投影的
 自然性（proj_*_natural）、余单位律（proj_*_diagonal）以及
 叉/投影往返 proj_left_right_diagonal。然后闭合的强制转换
 使每个笛卡尔单体范畴都可以作为笛卡尔范畴使用。
*)

Section CartesianMonoidalCartesian.

Context `{@CartesianMonoidal C}.

Program Definition CartesianMonoidal_Cartesian : @Cartesian C := {|
  product_obj := fun x y => (x ⨂ y)%object;   (* x × y := x ⨂ y *)
  Cartesian.fork := @fork _ _;                 (* ⟨f, g⟩ := (f ⨂ g) ∘ ∆ *)
  exl  := fun _ _ => proj_left;                (* first projection π₁ / 第一投影 π₁ *)
  exr  := fun _ _ => proj_right                (* second projection π₂ / 第二投影 π₂ *)
|}.
Next Obligation.
  (*
 ump_products: h ≈ ⟨f, g⟩ ↔ (exl ∘ h ≈ f) ∧ (exr ∘ h ≈ g).
 Forward: rewrite h to ⟨f, g⟩ = (f ⨂ g) ∘ ∆, slide each projection past
 the tensor by proj_*_natural, then collapse proj_* ∘ ∆ by the counit law
 proj_*_diagonal.  Backward: rebuild ⟨f, g⟩ from the two equations using
 bimap_comp, diagonal_natural, and the round-trip proj_left_right_diagonal. 

 --------
 ump_products: h ≈ ⟨f, g⟩ ↔ (exl ∘ h ≈ f) ∧ (exr ∘ h ≈ g)。
 正向：将 h 重写为 ⟨f, g⟩ = (f ⨂ g) ∘ ∆，通过 proj_*_natural 将每个投影滑过张量，然后通过辅元律 proj_*_diagonal 折叠 proj_* ∘ ∆。
 反向：使用 bimap_comp、diagonal_natural 和循环投影 proj_left_right_diagonal 从这两个方程重建 ⟨f, g⟩。
*)
  unfold fork.
  split; intros.
  - split.
    + rewrites.
      rewrite comp_assoc.
      rewrite proj_left_natural.
      rewrite <- comp_assoc.
      rewrite proj_left_diagonal; cat.
    + rewrites.
      rewrite comp_assoc.
      rewrite proj_right_natural.
      rewrite <- comp_assoc.
      rewrite proj_right_diagonal; cat.
  - rewrite <- (fst X), <- (snd X).
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    srewrite diagonal_natural.
    rewrite comp_assoc.
    rewrite proj_left_right_diagonal; cat.
Qed.

End CartesianMonoidalCartesian.

(* Every cartesian monoidal category is a cartesian category. / 每个笛卡尔单体范畴都是一个笛卡尔范畴。 *)
Coercion CartesianMonoidal_Cartesian : CartesianMonoidal >-> Cartesian.
