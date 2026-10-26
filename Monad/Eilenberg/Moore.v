Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.

Generalizable All Variables.

(** * The Eilenberg–Moore category of a monad.  / * 单子的艾伦伯格-摩尔范畴。*)

(*
nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   The Eilenberg–Moore category C^T of a monad (M, ret, join) = (T, η, μ) on C
   is the category of T-algebras and their homomorphisms (see Monad/Algebra.v).
   An object is a pair (a, ν) of a carrier a : C together with an action
   ν : T a ~> a (t_alg) satisfying the unit law ν ∘ η_a ≈ id and the
   associativity/action law ν ∘ T(ν) ≈ ν ∘ μ_a (t_id and t_action). A morphism
   (a, ν^a) ~> (b, ν^b) is an underlying C-morphism f : a ~> b that intertwines
   the actions, f ∘ ν^a ≈ ν^b ∘ T(f) (t_alg_hom_commutes).

   Identities and composition are inherited from C on the underlying carriers:
   id is id_a (which trivially commutes), and the composite of two algebra
   homomorphisms is again one — the obligation below pastes their two commuting
   squares, using fmap_comp for T(g ∘ f) and t_alg_hom_commutes twice.
   Equivalence of morphisms is equivalence of the underlying C-maps.

   The forgetful functor U^T : C^T → C, (a, ν) ↦ a, has the free-algebra
   functor F^T : C → C^T, x ↦ (T x, μ_x), as left adjoint, and the monad
   U^T ∘ F^T arising from F^T ⊣ U^T is exactly T; that adjunction is
   constructed in Monad/Eilenberg/Moore/Adjunction.v ([EM_Free] ⊣ [EM_Forget]
   as [EM_Adjunction], recovering T via [EM_Monad_agrees]). This is the
   terminal such resolution of T; the Kleisli category (see Monad/Kleisli.v,
   whose own resolution lives in Monad/Kleisli/Adjunction.v) is the initial
   one, sitting inside C^T as the full subcategory of free algebras.

   CORRECTION (#475).  “Sitting inside C^T” was asserted with no functor
   C_T ⟶ C^T in the tree; it is Monad/Kleisli/Comparison.v's [Kleisli_EM],
   full and faithful onto the free algebras.  The terminality and the
   initiality asserted here are Mac Lane's Theorem VI.5.3, which issue #476
   tracks. 

--------
nLab：https://ncatlab.org/nlab/show/Eilenberg-Moore+category
 维基百科：https://en.wikipedia.org/wiki/Monad_(category_theory)

C 上单子 (M, ret, join) = (T, η, μ) 的 Eilenberg-Moore 范畴 C^T
 是 T 代数及其同态的范畴（参见 Monad/Algebra.v）。 
一个对象是一对 (a, ν) 的载体 a : C 和一个动作
 ν : T a ~> a (t_alg) 满足单位律 ν ∘ η_a ≈ id 且
 结合性/作用定律 ν ∘ T(ν) ≈ ν ∘ μ_a（t_id 和 t_action）。 态射
 (a, ν^a) ~> (b, ν^b) 是一个潜在的 C 态射 f : a ~> b 交织在一起
 动作 f ∘ ν^a ≈ ν^b ∘ T(f) (t_alg_hom_commutes)。

身份和组成继承自底层载体上的 C：
 id 是 id_a （简单地交换），以及两个代数的复合
 同态又是其中之一——下面的义务粘贴了他们的两个通勤
 正方形，使用 fmap_comp 表示 T(g ∘ f) 并使用 t_alg_hom_commutes 两次。 
态射的等价性就是底层 C-map 的等价性。

健忘函子 U^T : C^T → C, (a, ν) ↦ a，具有自由代数
 函子 F^T : C → C^T, x ↦ (T x, μ_x)，作为左伴随，以及单子
 U^T ∘ F^T 由 F^T ⊣ U^T 产生，恰好是 T； 该附加项是
 在 Monad/Eilenberg/Moore/Adjunction.v 中构造（[EM_Free] ⊣ [EM_Forget]
 如 [EM_Adjunction]，通过 [EM_Monad_agrees] 恢复 T）。 这是
 终端T的分辨率； Kleisli 类别（参见 Monad/Kleisli.v，
 其自己的决议位于 Monad/Kleisli/Adjunction.v) 中
 一，作为自由代数的完整子范畴位于 C^T 中。

更正（#475）。 “坐在 C^T 内部”被断言，没有函子
 树中的 C_T ⟶ C^T； 它是 Monad/Kleisli/Comparison.v 的 [Kleisli_EM]，
 全面而忠实地研究自由代数。 终结性和
 这里断言的初始性是 Mac Lane 定理 VI.5.3，问题 #476
 曲目。 
*)

(*
The monad instance is bound by name so that [TAlgebra]'s instance argument
   can be given explicitly in [obj]: were it left to Program, the elaborator
   would seal that argument behind a Qed-opaque obligation constant, and
   algebras built against the ambient instance [H] — such as the free algebras
   (T a, μ_a) of Moore/Adjunction.v — would not be recognized as objects of
   this category. 

--------
monad 实例由名称绑定，以便 [TAlgebra] 的实例参数
 可以在 [obj] 中明确给出：是否留给程序，即阐述者
 会将这一论点密封在 Qed 不透明的义务常数后面，并且
 针对环境实例 [H] 构建的代数 — 例如自由代数
 Moore/Adjunction.v 的 (T a, μ_a) — 不会被识别为
 这个类别。 
*)

(*
   【EilenbergMoore 范畴定义展开】/ Definition walkthrough
   （口吻对齐 Theory/Functor.v @ c826572；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Eilenberg–Moore 范畴 C^T：对象是 T-代数 (a, ν : T a ~> a)；
      态射是与结构映射交换的底层箭头（代数同态）。见 Monad/Algebra.v。
      Objects = T-algebras; morphisms = algebra homs. See Monad/Algebra.v.
      Haskell 对照：可想成「带 join 相容结构的载体」；不如 Kleisli 常见于
      日常代码，但是单子「终结分解」的数学家侧。
      Less common in day-to-day Haskell; the terminal resolution of a monad.

   2) 关键字段 / Key Category fields
      - obj := ∃ a, TAlgebra T a
      - hom := TAlgebraHom（须 t_alg_hom ∘ ν_a ≈ ν_b ∘ T(-)）
      - id / compose 继承自 C 的底层 id/∘，义务验证仍是代数同态。
      相等是底层态射的 ≈。/ Equality = ≈ of underlying morphisms.

   3) 与 Kleisli / 伴随 / Relation
      自由代数函子 ⊣ 遗忘函子 恢复原单子 T（Moore/Adjunction.v）；
      Kleisli 是初始分解，EM 是终结分解。
      Free ⊣ Forget recovers T; Kleisli initial, EM terminal.

   阅读顺序：TAlgebra（Algebra.v）→ 本 Category → EM_Adjunction。
   Reading order: TAlgebra → this Category → EM_Adjunction.
*)

Program Definition EilenbergMoore `(T : C ⟶ C) `{H : @Monad C T} : Category := {|
  obj     := ∃ a : C, @TAlgebra C T H a;
  hom     := fun x y => TAlgebraHom T ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => t_alg_hom[f] ≈ t_alg_hom[g] |};
  id      := fun _ => {| t_alg_hom := id |};
  compose := fun _ _ _ f g => {| t_alg_hom := t_alg_hom[f] ∘ t_alg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- t_alg_hom_commutes.
  rewrite <- !comp_assoc.
  rewrite <- t_alg_hom_commutes.
  reflexivity.
Qed.
