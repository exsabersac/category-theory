Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(*
   * * Dagger categories

   nLab:      https://ncatlab.org/nlab/show/dagger+category
   Wikipedia: https://en.wikipedia.org/wiki/Dagger_category
   Book:      Mac Lane, "Categories for the Working Mathematician",
   2nd ed., GTM 5, §I.7 (printed p. 26): Rel carries the
   converse operation R† [maclane:I.7:construction8]
   Book:      Awodey, "Category Theory", 2nd ed., §1.9 Exercise 2
   (printed p. 29): the self-duality Rel ≅ Rel^op
   Paper:     Selinger, "Dagger compact closed categories and
   completely positive maps", ENTCS 170 (2007) — the modern
   axiomatization and the name

   A DAGGER CATEGORY is a category equipped with an
   identity-on-objects involution reversing every morphism: each
   f : x ~> y has a dagger f† : y ~> x with (f†)† ≈ f, id† ≈ id, and
   (f ∘ g)† ≈ g† ∘ f† — an anti-homomorphism for composition.  The
   concept axiomatizes "reversal" structure that a bare category
   cannot see: relation converse in Rel, adjoints of linear maps in
   Hilbert spaces, path reversal in groupoids.  Selinger's dagger
   compact closed categories are the semantic backbone of categorical
   quantum mechanics — the ZX-calculus prose in Instance/ZX.v and the
   compact-closed remarks in Structure/Monoidal/StarAutonomous.v both
   name daggers; this class is the light common vocabulary those
   discussions were missing (no compatibility with monoidal structure
   is demanded here — dagger monoidal/compact closed towers are left
   for the developments that need them).

   The class is deliberately minimal: the four laws above and nothing
   else, with the operation packaged as data ([dagger]) plus a
   [Proper] field so it respects the hom-setoids.  A dagger is
   equivalently an identity-on-objects functor C^op ⟶ C squaring to
   the identity; instances may expose that functor separately (as
   Instance/Rel/Dagger.v does for Rel, where it assembles into the
   self-duality isomorphism Rel ≅ Rel^op in Cat — Awodey's Exercise
   1.9.2(a)). 

   --------
   * * 匕首范畴

   nLab:       https://ncatlab.org/nlab/show/dagger+category 
   维基百科:  https://en.wikipedia.org/wiki/Dagger_category 
   书籍:      Mac Lane, 《为工作数学家而写的范畴论》, 第2版, GTM 5, §I.7 (印刷版第26页): Rel 包含逆运算 R†  [maclane:I.7:construction8] 
   书籍:      Awodey, 《范畴论》, 第2版, §1.9 练习2 (印刷版第29页): Rel 的自对偶性 Rel ≅ Rel^op
   论文:      Selinger, "匕首紧闭范畴和完全正映射", ENTCS 170 (2007) — 现代公理化及名称匕首范畴（DAGGER CATEGORY）是一个配备了对每个态射进行逆转的对象恒等的自反运算的范畴：对于每一个态射 f : x ~> y 都有一个匕首 f† : y ~> x，使得 (f†)† ≈ f，id† ≈ id，以及 (f ∘ g)† ≈ g† ∘ f† —— 对组成是一个反同态。该概念公理化了一个普通范畴无法看到的“逆转”结构：在 Rel 中的关系逆，希尔伯特空间中线性映射的伴随，以及群体（groupoids）中的路径逆转。塞林格的匕首
   紧致闭合范畴是范畴量子力学的语义基础——Instance/ZX.v 中的 ZX-演算文字说明和 Structure/Monoidal/StarAutonomous.v 中的紧致闭合备注都提到了匕首；这个类是那些讨论中缺失的轻量通用词汇（这里不要求与幺半结构的兼容性——匕首幺半/紧致闭合塔留给需要它们的开发使用）。这个类故意保持最简：仅包含上述四条定律，没有其他内容，并且将操作打包为数据（[dagger]）加上一个[Proper]字段，以便它遵循同类集合。同态标记。匕首(dagger)等价于一个在对象上是恒等的函子 C^op ⟶ C 并且平方为恒等；实例可能会单独暴露该函子（就像 Instance/Rel/Dagger.v 对 Rel 所做的那样，其中它组装成 Cat 中的自对偶同构 Rel ≅ Rel^op — 参考 Awodey 的练习 1.9.2(a)）。
*)

Class DaggerCategory (C : Category) := {
  dagger {x y : C} : (x ~> y) → (y ~> x);

  dagger_respects {x y : C} :
    Proper (equiv ==> equiv) (@dagger x y);

  dagger_involution {x y : C} (f : x ~> y) :
    dagger (dagger f) ≈ f;

  dagger_id {x : C} : dagger (@id C x) ≈ id;

  (*
 The anti-homomorphism law: reversal exchanges the order of
 composition. 

 --------
 反同态定律：逆序交换组合的顺序。
*)
  dagger_compose {x y z : C} (f : y ~> z) (g : x ~> y) :
    dagger (f ∘ g) ≈ dagger g ∘ dagger f
}.

#[export] Existing Instance dagger_respects.

Notation "f †" := (dagger f) (at level 30) : morphism_scope.
