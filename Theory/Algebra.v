Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.

Generalizable All Variables.

(* * * Categorified high-school algebra 双笛卡尔闭 范畴 （已译） *)

(* nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/rig+category
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_category

   本文件汇集别处已证结果（Structure/Cartesian.v、Structure/Cocartesian.v、
   Structure/Cartesian/Closed.v），展示范畴构造与基础中学代数之间的直接对应。
   在双笛卡尔闭范畴 (bicartesian closed category)——即笛卡尔（×，终对象 1）、
   余笛卡尔（+，初始对象 0）且笛卡尔闭（内部 hom，写作 x^y）——中，结构同构把
   rig（半环，即无负元的环）的恒等式范畴化：余积 + 像以 0 为单位的加法，积 × 像
   以 1 为单位且被 0 零化的乘法，× 对 + 分配，内部 hom x^y 扮演指数。把 ≅
   （「同构」）读作代数学家的 =，下文每个目标都是熟知算术定律的范畴化对应，例如
   x × (y + z) ≅ (x × y) + (x × z)、x^(y + z) ≅ x^y × x^z 与 x^(y × z) ≅ (x^y)^z
   （后者即 curry/uncurry 伴随）。每个目标都由这些预证同构的本地 hint 库经 [auto]
   消解，故本节不断言新内容；它是 BiCCC 结构已提供之代数的可读索引。 *)

Section BasicAlgebra.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
Context `{@Terminal C}.
Context `{@Initial C}.
Context `{@Cocartesian C}.

#[local] Hint Resolve coprod_zero_r : core.
#[local] Hint Resolve coprod_zero_l : core.
#[local] Hint Resolve coprod_comm : core.
#[local] Hint Resolve coprod_assoc : core.
#[local] Hint Resolve prod_zero_r : core.
#[local] Hint Resolve prod_zero_l : core.
#[local] Hint Resolve prod_one_r : core.
#[local] Hint Resolve prod_one_l : core.
#[local] Hint Resolve prod_assoc : core.
#[local] Hint Resolve prod_comm : core.
#[local] Hint Resolve exp_zero : core.
#[local] Hint Resolve exp_one : core.
#[local] Hint Resolve one_exp : core.
#[local] Hint Resolve prod_coprod_l : core.
#[local] Hint Resolve prod_coprod_r : core.
#[local] Hint Resolve exp_swap : core.
#[local] Hint Resolve exp_prod_l : core.
#[local] Hint Resolve exp_prod_r : core.
#[local] Hint Resolve exp_coprod : core.

#[local] Hint Extern 4 => intros x y z; transitivity ((x^z)^y); auto : core.

Goal ∀ x : C,        x + 0 ≅ x.                          auto. Qed.
Goal ∀ x : C,        0 + x ≅ x.                          auto. Qed.
Goal ∀ x y : C,      x + y ≅ y + x.                      auto. Qed.
Goal ∀ x y z : C,    (x + y) + z ≅ x + (y + z).          auto. Qed.

Goal ∀ x : C,        x × 0 ≅ 0.                          auto. Qed.
Goal ∀ x : C,        0 × x ≅ 0.                          auto. Qed.
Goal ∀ x : C,        x × 1 ≅ x.                          auto. Qed.
Goal ∀ x : C,        1 × x ≅ x.                          auto. Qed.
Goal ∀ x y z : C,    (x × y) × z ≅ x × (y × z).          auto. Qed.
Goal ∀ x y : C,      x × y ≅ y × x.                      auto. Qed.

Goal ∀ x y z : C,    x × (y + z) ≅ (x × y) + (x × z).    auto. Qed.
Goal ∀ x y z : C,    (x + y) × z ≅ (x × z) + (y × z).    auto. Qed.

Goal ∀ x : C,        x^0 ≅ 1.                            auto. Qed.
Goal ∀ x : C,        x^1 ≅ x.                            auto. Qed.
Goal ∀ x : C,        1^x ≅ 1.                            auto. Qed.
Goal ∀ x y z : C,    x^(y + z) ≅ x^y × x^z.              auto. Qed.
Goal ∀ x y z : C,    (x × y)^z ≅ x^z × y^z.              auto. Qed.
Goal ∀ x y z : C,    x^(y × z) ≅ (x^y)^z.                auto. Qed.

End BasicAlgebra.
