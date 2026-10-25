Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(*
 Derived equalities for the semicartesian (affine) monoidal structure: a
 monoidal category whose unit object I is terminal.  Terminality of I gives,
 for every object, a unique discard map `eliminate` x ~> I, and from it the
 two projections

 proj_left  = unit_right ∘ id ⨂ eliminate : x ⨂ y ~> x,
 proj_right = unit_left  ∘ eliminate ⨂ id : x ⨂ y ~> y.

 The lemmas below are the projection calculus that follows purely from this
 data, with no diagonal/copying assumed (that extra structure is what would
 make the category cartesian).  They split into three groups: the associator
 compatibilities proj_left_tensor_id / proj_right_tensor_id, the iterated
 projection equations proj_left_left / proj_right_right, and the projection
 naturality corollaries proj_left_natural / proj_right_natural.  Every step is
 discharged from the monoidal coherence axioms together with the terminality
 of I (used only through `eliminate` and `unit_terminal`/`eliminate_comp`).

 nLab:      https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 Wikipedia: no dedicated article; the unit-terminal condition is noted under
 https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 These establish that the projection maps a semicartesian category carries are
 natural and associate coherently with the tensor, i.e. that x ⨂ y behaves
 like a (weak, non-universal) "product-with-discarding" already at the affine
 level, before any diagonal is added. 

 --------
 半笛卡尔（仿射）单类结构的派生等式：一个单位对象 I 为终对象的单类范畴。I 的终性为每个对象提供了一个唯一的丢弃映射  `eliminate`  x ~> I，并由此得到两个投影

 proj_left  = unit_right ∘ id ⨂ eliminate : x ⨂ y ~> x,
 proj_right = unit_left  ∘ eliminate ⨂ id : x ⨂ y ~> y。下面的引理是从这些数据纯粹推导出的投影演算，没有假设对角线/复制（那种额外结构才会使该范畴是笛卡尔范畴）。它们分为三组：结合子兼容性 proj_left_tensor_id / proj_right_tensor_id，迭代投影方程 proj_left_left / proj_right_right，以及投影自然性推论 proj_left_natural / proj_right_natural。每一步都源自幺半范畴的一致性公理以及 I 的终对象性（仅通过 `eliminate` 和 `unit_terminal` / `eliminate_comp` 使用）。

 nLab:       https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 Wikipedia: 没有专门的条目；单位-终对象条件在 https://en.wikipedia.org/wiki/Cartesian_monoidal_category 下有提到这些表明，投影映射在半笛卡尔范畴中是自然的，并且与张量一致地关联，即 x ⨂ y 在仿射层面上已经表现得像一个（弱的、非通用的）“带丢弃的积”，在添加任何对角线之前。
*)

Section SemicartesianProofs.

Context `{@Monoidal C}.
Context `{@SemicartesianMonoidal C _}.

(*
 Associator compatibility of the left projection: projecting the left pair of
 a triple tensor and re-tensoring with id on the right agrees, across the
 associator (x ⨂ y) ⨂ z ~> x ⨂ (y ⨂ z), with discarding the inner z by the
 right projection on the right factor.  Both sides discard exactly z, so this
 is the triangle/associativity coherence of the discard map. 

 --------
 左投影的结合子兼容性：将三重张量的左对投影后，再与右侧的恒等张量重新张量化，与关联子 (x ⨂ y) ⨂ z ~> x ⨂ (y ⨂ z) 一致，同时通过右因子上的右投影丢弃内部的 z。两边都恰好丢弃 z，因此这是丢弃映射的三角形/结合性相容性。
*)
Lemma proj_left_tensor_id {x y z} :
  proj_left ⨂ id ≈ id[x] ⨂ @proj_right _ _ _ y z ∘ tensor_assoc.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_right.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal; reflexivity.
Qed.

(*
 The mirror image of proj_left_tensor_id: re-tensoring the right projection
 with id on the left agrees, across the inverse associator, with discarding
 the inner x by the left projection on the left factor.  Both sides discard
 exactly x. 

 --------
 proj_left_tensor_id 的镜像：在左边使用 id 对右投影重新张量化，通过逆结合变换，与在左因子上通过左投影丢弃内部 x 相一致。两边都精确地丢弃 x。
*)
Lemma proj_right_tensor_id {x y z} :
  id ⨂ proj_right ≈ @proj_left _ _ _ x y ⨂ id[z] ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_left, proj_right.
  rewrite bimap_comp_id_left.
  rewrite inverse_triangle_identity.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  normal; reflexivity.
Qed.

(*
 Iterated left projection: projecting (x ⨂ y) ⨂ z down to x ⨂ y and then to x
 is the same as re-associating to x ⨂ (y ⨂ z) and projecting straight onto x.
 Both routes discard y and z and keep x, so they agree; this is the
 associativity coherence between the projection and the associator. 

 --------
 迭代左投影：将 (x ⨂ y) ⨂ z 投影到 x ⨂ y 然后再投影到 x，
 与重新结合为 x ⨂ (y ⨂ z) 并直接投影到 x 是相同的。
 两条路径都舍弃 y 和 z 并保留 x，所以它们是一致的；
 这是投影与结合子之间的结合性相容性。
*)
Lemma proj_left_left {x y z} :
  proj_left ∘ proj_left ≈ @proj_left _ _ _ x (y ⨂ z) ∘ tensor_assoc.
Proof.
  unfold proj_left; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_right).
  rewrite to_unit_right_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_right.
  rewrite <- comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [reflexivity|].
  apply unit_terminal.
Qed.

(*
 The mirror image of proj_left_left: projecting x ⨂ (y ⨂ z) down to y ⨂ z and
 then to z equals re-associating to (x ⨂ y) ⨂ z and projecting straight onto
 z.  Both routes discard x and y and keep z. 

 --------
 proj_left_left 的镜像：将 x ⨂ (y ⨂ z) 投影到 y ⨂ z，然后再投影到 z 等于重新结合为 (x ⨂ y) ⨂ z 并直接投影到 z。两条路径都丢弃 x 和 y，只保留 z。
*)
Lemma proj_right_right {x y z} :
  proj_right ∘ proj_right ≈ @proj_right _ _ _ (x ⨂ y) z ∘ tensor_assoc⁻¹.
Proof.
  unfold proj_right; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ unit_left).
  rewrite to_unit_left_natural; normal.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite bimap_triangle_left.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [|reflexivity].
  apply unit_terminal.
Qed.

(*
 Naturality of the left projection: projecting after acting by f ⨂ g equals
 acting by f after projecting.  The discarded g is killed by eliminate_comp
 (eliminate ∘ g ≈ eliminate, since I is terminal), leaving only f.  This is the
 naturality square of proj_left as a transformation (- ⨂ =) ⟹ pr1. 

 --------
 左投影的自然性：在作用 f ⨂ g 之后投影等于在投影后作用 f。被丢弃的 g 被 eliminate_comp 消去（eliminate ∘ g ≈ eliminate，因为 I 是终对象），只剩下 f。这是 proj_left 作为一个变换 (- ⨂ =) ⟹ pr1 的自然性方形。
*)
Corollary proj_left_natural {x y z w} (f : x ~> y) (g : z ~> w) :
  proj_left ∘ f ⨂ g ≈ f ∘ proj_left.
Proof.
  unfold proj_left.
  rewrite comp_assoc.
  rewrite to_unit_right_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(*
 Naturality of the right projection, dual to proj_left_natural: the discarded
 f is killed by eliminate_comp, leaving only g.  This is the naturality square
 of proj_right as a transformation (- ⨂ =) ⟹ pr2. 

 --------
 右投影的自然性，与 proj_left_natural 对偶：被丢弃的 f 被 eliminate_comp 消去，只剩下 g。这是 proj_right 作为一个自然变换 (- ⨂ =) ⟹ pr2 的自然性方形。
*)
Corollary proj_right_natural {x y z w} (f : x ~> y) (g : z ~> w) :
  proj_right ∘ f ⨂ g ≈ g ∘ proj_right.
Proof.
  unfold proj_right.
  rewrite comp_assoc.
  rewrite to_unit_left_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End SemicartesianProofs.
