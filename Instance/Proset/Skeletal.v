Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Skeleton.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Partial orders are exactly the skeletal preorders / * * 偏序恰好是骨架上的预序 *)

(*
 nLab: https://ncatlab.org/nlab/show/poset
 nLab: https://ncatlab.org/nlab/show/skeleton
 Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

 Fong & Spivak define a partial order as a preorder satisfying x ≅ y → x
 = y (Seven Sketches in Compositionality, §1.2.2, remark 35, p. 13),
 observing that this condition is skeletality in categorical language; and
 Instance/Poset.v's own header has long said that antisymmetry "only makes
 the resulting thin category skeletal, so that isomorphic objects are
 equal", citing nLab's characterization of a poset as "a skeletal thin
 category".  Until Theory/Skeleton.v there was no [Skeletal] predicate to
 say it with, and the fact was exemplified only by two per-instance
 antisymmetry lemmas in the regression-guard file Test/Poset.v.

 [Proset_Skeletal_iff_Antisymmetric] states it, in both directions, for an
 arbitrary preorder.  The forward direction works because a [Proset]'s
 hom-setoid identifies all parallel morphisms (Instance/Proset.v), so both
 isomorphism laws are trivially satisfied and an isomorphism [x ≅ y] is
 exactly a pair of relation proofs.  [Poset_Skeletal] is the corollary for
 Instance/Poset.v's [Poset], which is DEFINITIONALLY a [Proset] — the
 antisymmetry argument does not appear in the body — and [Nat_le_Skeletal]
 instantiates it at (nat, ≤).

 Riehl computes that "the skeleton of a preorder is a poset" (Category
 Theory in Context, §1.5, Example 1.5.18, p. 37).  The honest in-tree form
 of that clause is [skeleton_of_proset_antisymmetric]: given a [Skeleton]
 of a preorder, its carriers satisfy antisymmetry.  The posetal
 REFLECTION — that every preorder HAS a skeleton — is a different
 statement and is not made here; see the note at the end of
 Theory/Skeleton.v. 

 --------
 nLab: https://ncatlab.org/nlab/show/poset
 nLab: https://ncatlab.org/nlab/show/skeleton
 Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

 Fong 和 Spivak 将偏序定义为满足 x ≅ y → x = y 的预序（《组合性七讲》，§1.2.2，注释 35，第 13 页），并观察到这个条件在范畴语言中即为骨架性；而 Instance/Poset.v 自身的文件头早已指出反对称性“仅使生成的薄范畴成为骨架范畴，因此同构对象相等”，并引用 nLab 对偏序集的描述为“骨架薄范畴”。直到 Theory/Skeleton.v 之前，没有 [Skeletal] 谓词来表达这一点，这一事实仅通过 regression-guard 文件 Test/Poset.v 中的两个每实例反对称性引理得以示例。[Proset_Skeletal_iff_Antisymmetric] 对于任意的预序关系，在两个方向上都声明了它。正向方向可行，因为 [Proset] 的同态集等价类（hom-setoid）会识别所有平行的态射（Instance/Proset.v），所以两个同构定律都是显然满足的，并且一个同构 [x ≅ y] 恰好是一对关系证明。[Poset_Skeletal] 是针对 Instance/Poset.v 的 [Poset] 的推论，它在定义上是一个 [Proset]——反对称性论证未出现在主体中——且 [Nat_le_Skeletal] 在 (nat, ≤) 上实例化了它。Riehl 计算得出“预序的骨架是一个偏序集”（《上下文中的范畴论》，§1.5，例 1.5.18，第 37 页）。该条款的真实树状形式是 [skeleton_of_proset_antisymmetric]：给定一个预序的 [Skeleton]，其载体满足反对称性。偏序的反射 —— 每个预序都有一个骨架 —— 是一个不同的陈述，并未在此提出；请参阅 Theory/Skeleton.v 末尾的注释。
*)

Section ProsetSkeletal.
Context {A : Type}.
Context {R : relation A}.
Variable P : PreOrder R.

(* * ** Seven Sketches §1.2.2 remark 35, both directions / * ** 七种素描 §1.2.2 注释 35，两个方向 *)

Theorem Proset_Skeletal_iff_Antisymmetric :
  (Skeletal (Proset P) → @Antisymmetric A eq eq_equiv R) *
  (@Antisymmetric A eq eq_equiv R → Skeletal (Proset P)).
Proof.
  split.
  - intros Sk x y Rxy Ryx.
    apply (Sk x y).
    exists Rxy Ryx; exact I.
  - intros Anti x y i.
    exact (Anti x y (to i) (from i)).
Qed.

Theorem Poset_Skeletal `{Anti : @Antisymmetric A eq eq_equiv R} :
  Skeletal (@Poset A R P Anti).
Proof. intros x y i. exact (Anti x y (to i) (from i)). Qed.

(*
 Both Instance/Proset.v and Instance/Poset.v define a constant of this
 name, and this file imports both, so the name is qualified explicitly rather than left to import order. 

 --------
 Instance/Proset.v 和 Instance/Poset.v 都定义了这个名称的常量，而这个文件导入了两者，所以该名称是明确限定的，而不是依赖导入顺序。
*)

Lemma Nat_le_Skeletal : Skeletal Poset.LessThanEqualTo_Category.
Proof.
  intros x y i.
  exact (partial_order_antisym PeanoNat.Nat.le_partialorder x y (to i) (from i)).
Qed.

(* * ** Riehl Example 1.5.18: the skeleton of a preorder is a poset / * ** Riehl 示例 1.5.18：预序的骨架是一个偏序集 *)

Theorem skeleton_of_proset_antisymmetric (S : Skeleton (Proset P))
        (a b : skel_cat S) :
  R (`1 a) (`1 b) → R (`1 b) (`1 a) → `1 a = `1 b.
Proof.
  intros f g.
  apply (f_equal (fun z : skel_cat S => `1 z)).
  apply (skeleton_is_skeletal S).
  exists (f; skel_full S _ _ `2 a `2 b f) (g; skel_full S _ _ `2 b `2 a g);
    exact I.
Qed.

(*
 A poset is its own skeleton, by the trivial route of
 [Skeleton_of_Skeletal].  This is a convenience for callers who want a
 [Skeleton] datum over an order; the content is in the theorems above. 

 --------
 一个偏序集本身就是它的骨架，通过平凡的途径 [Skeleton_of_Skeletal]。这对希望在一个序上获得 [Skeleton] 数据的调用者来说是方便的；其内容在上述定理中。
*)

Definition Proset_Skeleton (Anti : @Antisymmetric A eq eq_equiv R) :
  Skeleton (Proset P) :=
  Skeleton_of_Skeletal (snd Proset_Skeletal_iff_Antisymmetric Anti).

End ProsetSkeletal.
