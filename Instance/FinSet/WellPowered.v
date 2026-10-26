Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(** * FinSet is well-powered / * FinSet 是良有力的 *)

(*
 nLab:      https://ncatlab.org/nlab/show/well-powered+category
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §V.8,
 book p. 130: a category is well-powered when the subobjects of each
 object form a small set.  For the skeleton of finite sets this is the
 elementary fact that a finite set of size n has 2^n subsets, and the
 formal witness below reads it off the subobject classifier: the index
 at [n] is the hom-set [n ~> Ω], the characteristic functions
 [Fin.t n → Fin.t 2].

 WHAT IS DELIVERED.  [FinSet_WellPowered : WellPowered FinSet], an
 instance of Structure/WellPowered.v's [Classifier_WellPowered] at
 Instance/FinSet/Classifier.v's [FinSet_Pullbacks] and
 [FinSet_Classifier], and [FinSet_wp_index], the index read back at
 [eq_refl] as the functions [Fin.t n → Fin.t 2].  Both are
 unconditional: FinSet's classifier is the one in the tree that needs
 no hypothesis.  Every other [SubobjectClassifier] constructed in tree
 takes one -- [Untruncate] (Instance/Sets/Classifier/OneLevel.v's
 [Sets_Classifier], Instance/Fun/Classifier.v's [Fun_Classifier],
 [Fun_Classifier_cov] and [Fun_Classifier_small]), [IEM]
 ([Sets_Classifier_IEM], [Fun_Classifier_IEM]), [DecImage]
 ([Sets_Classifier_dec]) or [SmallClassifierExt]
 ([classifier_of_small]) -- by a grep for definitions whose type is a
 [SubobjectClassifier].

 UNIVERSES, measured with [Set Printing Universes. About
 FinSet_WellPowered.]:

 FinSet_WellPowered@{o h s t u v u0 u1} :
 WellPowered@{o h h s t} FinSet@{o h u v}
 ( * Set < u, h < t, o <= s, h <= s, and stdlib bounds * )

 The index sits at the hom universe [h] itself, the pinned reading of
 Structure/WellPowered.v, and no bound relates the object universe [o]
 to [h]: FinSet's objects are numerals, so the trivial witness
 [trivial_small] would also serve wherever [o <= h], but the classifier
 witness holds at every instantiation.

 NOT DELIVERED.  FinSet is finitely complete (Instance/FinSet/Limit.v's
 [FinSet_FinitelyComplete]) and carries no [Complete] instance, as it
 lacks infinite products, so Structure/WellPowered.v's intersection
 theorem, which takes [Complete], does not apply here; the binary meets
 of subobjects of a finite set are Theory/Subobject/Lattice.v's
 [sub_meet] at
 [FinSet_Pullbacks], as the header of Instance/FinSet/Subobject.v
 records.  No co-well-poweredness witness for FinSet is attempted. 

 --------
 nLab:       https://ncatlab.org/nlab/show/well-powered+category 
 nLab:       https://ncatlab.org/nlab/show/FinSet 
 维基百科:  https://en.wikipedia.org/wiki/Subobject_classifier 

 Mac Lane，《面向工作数学家的范畴论》，第2版，第V.8节，
 书页130: 当每个对象的子对象形成一个小集合时，范畴是良幂的。对于有限集的骨架，这是一个基本事实：大小为n的有限集有2^n个子集，下面的形式证明通过子对象分类器来读取它：在[n]处的指标是同集[n ~> Ω]，特征函数[Fin.t n → Fin.t 2]。交付内容。[FinSet_WellPowered : WellPowered FinSet]，一个 Structure/WellPowered.v 的 [Classifier_WellPowered] 实例，在 Instance/FinSet/Classifier.v 的 [FinSet_Pullbacks] 和 [FinSet_Classifier]，以及 [FinSet_wp_index]，作为 [Fin.t n → Fin.t 2] 函数在 [eq_refl] 读取回的索引。两者都是无条件的：FinSet 的分类器是在树中不需要假设的那个。树中构造的每个其他 [SubobjectClassifier] 都需要一个——[Untruncate]（Instance/Sets/Classifier/OneLevel.v 的 [Sets_Classifier]，Instance/Fun/Classifier.v 的 [Fun_Classifier]，[Fun_Classifier_cov] 和 [Fun_Classifier_small]），[IEM]（[Sets_Classifier_IEM]，[Fun_Classifier_IEM]），[DecImage]（[Sets_Classifier_dec]）或 [SmallClassifierExt]（[classifier_of_small]）——通过搜索类型为 [SubobjectClassifier] 的定义得到。

 宇宙，通过 [Set Printing Universes. About FinSet_WellPowered.] 测量：FinSet_WellPowered@{o h s t u v u0 u1} :
 WellPowered@{o h h s t} FinSet@{o h u v}
 ( * 集合 < u, h < t, o <= s, h <= s，以及标准库界限 * )

 索引位于同构宇宙 [h] 本身，这是 Structure/WellPowered.v 的固定读法，并且没有界限将对象宇宙 [o] 与 [h] 关联起来：FinSet 的对象是数字，因此平凡的证人 [trivial_small] 也可以在 [o <= h] 处使用，但分类器证人在每个实例化中都成立。未交付。FinSet 是有限完备的（Instance/FinSet/Limit.v 的 [FinSet_FinitelyComplete]），并且不具有 [Complete] 实例，因为它缺少无限积，因此 Structure/WellPowered.v 的交集定理，该定理适用于 [Complete]，在此不适用；有限集合的子对象的二元交是 Theory/Subobject/Lattice.v 的 [sub_meet]，如 Instance/FinSet/Subobject.v 的头部 [FinSet_Pullbacks] 所记录的。没有尝试为 FinSet 提供共良幂性证据。
*)

Definition FinSet_WellPowered@{o h s t u v +|
    Set < u, h < t, o <= s, h <= s +} :
  WellPowered@{o h h s t} FinSet@{o h u v} :=
  Classifier_WellPowered FinSet@{o h u v}.

(* The index at [n]: the characteristic functions of the subsets of n. / [n] 的指数：n 的子集的特征函数。 *)
Example FinSet_wp_index (n : FinSet) :
  wp_index (FinSet_WellPowered n) = (Fin.t n → Fin.t 2) := eq_refl.
