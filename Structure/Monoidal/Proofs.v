Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 These are the derived unit-coherence lemmas of a monoidal category: the
 consequences of the triangle and pentagon axioms (and the naturality of
 the unitors and associator) that Mac Lane's coherence theorem guarantees
 without making them part of the data. They are sometimes called Kelly's
 lemmas, after G. M. Kelly, “On MacLane's conditions for coherence of
 natural associativities, commutativities, etc.” (J. Algebra 1, 1964),
 which showed that several of the original Mac Lane axioms are redundant.
 What is established here:

 - left/right tensoring by id[I] is injective on morphisms;
 - id ⨂ λ ≈ λ and ρ ⨂ id ≈ ρ at the appropriate objects
 (Etingof et al., Proposition 2.2.2);
 - the variant triangle identities relating each unitor to the
 associator (e.g. λ ⨂ id ≈ λ ∘ α);
 - the pentagon identity in the inverse (α⁻¹) direction;
 - λ_I ≈ ρ_I, the two unitors agree on the unit object
 (Kelly 1964; [unit_identity]).

 Orientation note: as in [Structure/Monoidal.v], the associator is taken
 as α : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z), following nLab. Some sources use the
 opposite orientation; the statements below differ from those only by
 inverses. 

 --------
 nLab:  https://ncatlab.org/nlab/show/monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories 
 Wikipedia:  https://en.wikipedia.org/wiki/Monoidal_category 

 这些是单体范畴的派生单位一致性引理：它们是三角形和五边形公理的结果（以及恒等子函子和结合子的自然性），Mac Lane 的一致性定理保证这些结果成立，而无需将其作为数据的一部分。它们有时被称为 Kelly 引理，以纪念 G. M. Kelly，《On MacLane's conditions for coherence of natural associativities, commutativities, etc.》（J. Algebra 1, 1964），该文展示了最初的几条 Mac Lane 公理是多余的。此处确立的是：- 左/右 与 id [I] 的张量作用在态射上是单射的；
 - 在适当的对象上，id ⨂ λ ≈ λ 且 ρ ⨂ id ≈ ρ（Etingof 等, 命题 2.2.2）；
 - 关联每个单位子与结合子相关的变体三角恒等式（例如 λ ⨂ id ≈ λ ∘ α）；
 - 逆方向（α⁻¹）的五边形恒等式；
 - λ_I ≈ ρ_I，两者在单位对象上相同（Kelly 1964；[unit_identity]）。

 方向说明：如 [Structure/Monoidal.v] 中，结合子取为 α : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z)，参照 nLab。一些资料使用相反方向；以下陈述仅与那些不同在取了逆元素。
*)

Section MonoidalProofs.

Context `{M : @Monoidal C}.

(*
 Left tensoring by id[I] reflects equality of morphisms: it is a faithful
 operation because λ (unit_left) is a natural isomorphism. Used to cancel a
 leading [id[I] ⨂ -] when deriving the variant triangle identities. 

 --------
 通过 id [I] 的左张量反映了态射的相等性：它是一个忠实操作，因为 λ（unit_left）是一个自然同构。在推导变体三角恒等式时，用于消去前导的 [id[I] ⨂ -].
*)

Lemma tensor_id_left_inj {x y} (f g : x ~> y) :
  id[I] ⨂ f ≈ id[I] ⨂ g → f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_left).
  rewrite !comp_assoc.
  rewrite !to_unit_left_natural.
  rewrites; reflexivity.
Qed.

(*
 The mirror of [tensor_id_left_inj]: right tensoring by id[I] is faithful,
 since ρ (unit_right) is a natural isomorphism. 

 --------
 [tensor_id_left_inj] 的镜像：通过 id [I] 的右张量是忠实的，因为 ρ（unit_right）是一个自然同构。
*)

Lemma tensor_id_right_inj {x y} (f g : x ~> y) :
  f ⨂ id[I] ≈ g ⨂ id[I] → f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_right).
  rewrite !comp_assoc.
  rewrite !to_unit_right_natural.
  rewrites; reflexivity.
Qed.

(* The following proofs are from the book “Tensor Categories”, by Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, and Victor Ostrik. / 以下证明来自Pavel Etingof、Shlomo Gelaki、Dmitri Nikshych 和 Victor Ostrik 合著的《张量范畴》一书。 *)

(* Proposition 2.2.2 / 命题 2.2.2 *)

(*
 The left unitor is compatible with the tensor on the unit side:
 id[I] ⨂ λ_x ≈ λ_{I ⨂ x}. Following Etingof et al., this is read off from
 naturality of λ (the square below) together with λ being an isomorphism. 

 --------
 左单位元与单位侧的张量兼容：
 id [I] ⨂ λ_x ≈ λ_{I ⨂ x}。按照 Etingof 等人的说法，这可以从 λ 的自然性（下面的方形图）以及 λ 是一个同构推出来。
*)

Proposition id_unit_left {x} :
  id ⨂ unit_left ≈ @unit_left _ _ (I ⨂ x).
Proof.
  (*
 “It follows from naturality of the left unit constraint l that the
 following diagram commutes...” 

 --------
 由左单位约束 l 的自然性可得，以下图表交换...
*)
  assert (unit_left ∘ id ⨂ unit_left
            << I ⨂ (I ⨂ x) ~~> x >>
            unit_left ∘ unit_left)
    by (rewrite to_unit_left_natural; reflexivity).

  (* “Since lX is an isomorphism, the first identity follows.” / 由于 lX 是同构，第一个等式成立。 *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_left).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

(*
 The mirror of [id_unit_left] for the right unitor:
 ρ_x ⨂ id[I] ≈ ρ_{x ⨂ I}, from naturality of ρ and ρ being an iso. 

 --------
 右单位元的 [id_unit_left] 的镜像：
 ρ_x ⨂ id [I]  ≈ ρ_{x ⨂ I}，由 ρ 的自然性以及 ρ 是同构得出。
*)

Proposition id_unit_right {x} :
  unit_right ⨂ id ≈ @unit_right _ _ (x ⨂ I).
Proof.
  (*
 “It follows from naturality of the left unit constraint l that the
 following diagram commutes...” 

 --------
 由左单位约束 l 的自然性可得，以下图表交换...
*)
  assert (unit_right ∘ unit_right ⨂ id
            << (x ⨂ I) ⨂ I ~~> x >>
          unit_right ∘ unit_right)
    by (rewrite to_unit_right_natural; reflexivity).

  (* “The second one follows similarly from naturality of r.” / 第二个同样可以从 r 的自然性推导出来。 *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_right).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

(* Proposition 2.2.4 / 命题 2.2.4 *)

(*
 Helper diagram for the variant left triangle identity. It expresses the
 commutativity of the “lower right triangle” obtained by pasting the
 associator-naturality square against the pentagon and the triangle axiom;
 [triangle_identity_left] is recovered from it by specializing x = I and
 cancelling the leading [id[I] ⨂ -] via [tensor_id_left_inj]. 

 --------
 变体左三角恒等式的辅助图。它表达了通过将结合子自然性方形粘贴到五边形和三角公理上得到的“右下三角形”的交换性；通过取 x = I 并通过 [tensor_id_left_inj] 消去前导的 [id[I] ⨂ -，可以从中恢复 [triangle_identity_left]。
*)

Lemma bimap_id_unit_left {x y z} :
  id ⨂ (unit_left ⨂ id)
    << x ⨂ ((I ⨂ y) ⨂ z) ~~> x ⨂ (y ⨂ z) >>
  id ⨂ unit_left ∘ id ⨂ tensor_assoc.
Proof.
  (* “Consequently, the lower right triangle commutes as well.” / 因此，下右三角形也可交换。 *)
  pose proof (to_tensor_assoc_natural (id[x]) (@unit_left _ _ y) (id[z])) as X0.
  assert (X1 : ∀ x y z w (f g : (x ⨂ y) ⨂ z ~> w),
             f ≈ g → f ∘ tensor_assoc⁻¹ ≈ g ∘ tensor_assoc⁻¹).
  { intros; rewrites; reflexivity. }
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_to_from, id_right in X0.
  rewrites.
  rewrite comp_assoc; normal.

  pose proof (to_tensor_assoc_natural
                (@unit_right _ _ x) (id[y]) (id[z])) as X0.
  rewrite bimap_id_id in X0.
  rewrite triangle_identity in X0.
  rewrite triangle_identity in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- pentagon_identity in X0.
  rewrite !comp_assoc in X0.
  normal.
  symmetry in X0.
  rewrite bimap_comp_id_right in X0.
  rewrite comp_assoc in X0.

  assert (X2 : ∀ (f g : (x ⨂ I ⨂ y) ⨂ z ~{ C }~> x ⨂ y ⨂ z),
             f ∘ tensor_assoc ⨂ id ≈ g ∘ tensor_assoc ⨂ id
             → f ≈ g). {
    intros.
    assert (X3 : ∀ x y z w v (f g : ((x ⨂ y) ⨂ z) ⨂ v ~> w),
               f ≈ g → f ∘ (tensor_assoc⁻¹ ⨂ id[v]) ≈
                        g ∘ (tensor_assoc⁻¹ ⨂ id[v])). {
      intros; rewrites; reflexivity.
    }
    apply X3 in X.
    normal.
    rewrite !iso_to_from in X.
    rewrite !bimap_id_id, !id_right in X.
    assumption.
  }
  apply X2 in X0; clear X2.
  rewrites.

  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(*
 Variant triangle identity, the unit-on-the-left form: λ ⨂ id ≈ λ ∘ α.
 This is Kelly's lemma λ_x ⨂ id_y ≈ λ_{x ⨂ y} ∘ α_{I,x,y}, a derived
 coherence consequence (not part of the monoidal data). 

 --------
 变体三角恒等式，左边单位形式：λ ⨂ id ≈ λ ∘ α。这是凯利引理 λ_x ⨂ id_y ≈ λ_{x ⨂ y} ∘ α_{I,x,y}，一个推导出的相容性结果（不是单体范畴数据的一部分）。
*)

Theorem triangle_identity_left {x y} :
  unit_left ⨂ id
    << (I ⨂ x) ⨂ y ~~> x ⨂ y >>
  unit_left ∘ tensor_assoc.
Proof.
  (*
 “Setting x = 1 and applying the functor L−1 to the lower right triangle,
 1 we obtain commutativity of the triangle (2.12).” 

 --------
 将 x 设为 1 并将函子 L−1 应用于右下三角形，1 我们得到三角形 (2.12) 的可交换性。
*)
  pose proof (@bimap_id_unit_left I x y).
  normal.
  apply tensor_id_left_inj in X.
  assumption.
Qed.

(*
 The original triangle axiom (ρ ⨂ id ≈ id ⨂ λ ∘ α) rewritten across the
 inverse associator: id ⨂ λ ≈ (ρ ⨂ id) ∘ α⁻¹. Just the axiom post-composed
 with α⁻¹ and simplified, so no new content beyond [triangle_identity]. 

 --------
 原始三角公理 (ρ ⨂ id ≈ id ⨂ λ ∘ α) 通过逆结合子改写为：id ⨂ λ ≈ (ρ ⨂ id) ∘ α⁻¹。只是将公理与 α⁻¹ 后组合并简化，所以没有超出 [triangle_identity] 的新内容。
*)

Theorem inverse_triangle_identity {x y} :
  id ⨂ unit_left
    << x ⨂ (I ⨂ y) ~~> x ⨂ y >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

(*
 The pentagon axiom in the inverse (α⁻¹) direction, obtained by inverting
 both sides of [pentagon_identity] and reversing the composition order:
 (α⁻¹ ⨂ id) ∘ α⁻¹ ∘ (id ⨂ α⁻¹) ≈ α⁻¹ ∘ α⁻¹. Used by [bimap_unit_right_id]. 

 --------
 在逆方向 (α⁻¹) 的五边形公理，通过对 [pentagon_identity] 的两边取逆并反转组合顺序得到：
 (α⁻¹ ⨂ id) ∘ α⁻¹ ∘ (id ⨂ α⁻¹) ≈ α⁻¹ ∘ α⁻¹。由 [bimap_unit_right_id] 使用。
*)

Theorem inverse_pentagon_identity {x y z w} :
  tensor_assoc⁻¹ ⨂ id[w] ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ tensor_assoc⁻¹
      << x ⨂ (y ⨂ (z ⨂ w)) ~~> ((x ⨂ y) ⨂ z) ⨂ w >>
  tensor_assoc⁻¹ ∘ tensor_assoc⁻¹.
Proof.
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  apply (iso_to_epic tensor_assoc).
  rewrite iso_from_to.
  rewrite <- !comp_assoc.
  rewrite <- pentagon_identity.
  normal.
  rewrite iso_from_to; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to; normal.
  rewrite iso_from_to; normal.
  reflexivity.
Qed.

(*
 Right-handed mirror of [bimap_id_unit_left]: the helper diagram from which
 [triangle_identity_right] is recovered. Built by pasting the inverse
 associator-naturality square against the inverse pentagon and the inverse
 triangle identity, then cancelling the trailing [- ⨂ id]. 

 --------
 [bimap_id_unit_left] 的右手镜像：从中恢复 [triangle_identity_right] 的辅助图。通过将逆结合子自然性方形粘贴到逆五边形和逆三角恒等式上构建，然后消去尾部的 [- ⨂ id]。
*)

Lemma bimap_unit_right_id {x y z} :
  (id ⨂ unit_right) ⨂ id
    << (x ⨂ (y ⨂ I)) ⨂ z ~~> (x ⨂ y) ⨂ z >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹ ⨂ id.
Proof.
  (* “Consequently, the lower right triangle commutes as well.” / 因此，下右三角形也可交换。 *)
  pose proof (from_tensor_assoc_natural
                (id[x]) (@unit_right _ _ y) (id[z])) as X0.
  assert (X1 : ∀ x y z w (f g : x ⨂ (y ⨂ z) ~> w),
             f ≈ g → f ∘ tensor_assoc ≈ g ∘ tensor_assoc). {
    intros; rewrites; reflexivity.
  }
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_from_to, id_right in X0.
  rewrites.
  rewrite comp_assoc; normal.

  pose proof (from_tensor_assoc_natural
                (id[x]) (id[y]) (@unit_left _ _ z)) as X0.
  rewrite bimap_id_id in X0.
  rewrite inverse_triangle_identity in X0.
  rewrite inverse_triangle_identity in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- inverse_pentagon_identity in X0.
  rewrite !comp_assoc in X0.
  normal.
  symmetry in X0.
  rewrite bimap_comp_id_left in X0.
  rewrite comp_assoc in X0.

  assert (X2 : ∀ (f g : x ⨂ ((y ⨂ I) ⨂ z) ~{ C }~> (x ⨂ y) ⨂ z),
             f ∘ id ⨂ tensor_assoc⁻¹ ≈ g ∘ id ⨂ tensor_assoc⁻¹
             → f ≈ g). {
    intros.
    assert (X3 : ∀ x y z w v (f g : x ⨂ (y ⨂ (z ⨂ v)) ~> w),
               f ≈ g → f ∘ (id[x] ⨂ tensor_assoc) ≈
                        g ∘ (id[x] ⨂ tensor_assoc)). {
      intros; rewrites; reflexivity.
    }
    apply X3 in X.
    normal.
    rewrite !iso_from_to in X.
    rewrite !bimap_id_id, !id_right in X.
    assumption.
  }
  apply X2 in X0; clear X2.
  rewrites.

  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

(*
 Variant triangle identity, the unit-on-the-right form: id ⨂ ρ ≈ ρ ∘ α⁻¹.
 The Kelly lemma ρ_{x ⨂ y} ≈ (id_x ⨂ ρ_y) ∘ α_{x,y,I}, here stated across
 α⁻¹; the right-handed companion of [triangle_identity_left]. 

 --------
 变体三角恒等式，右单元形式：id ⨂ ρ ≈ ρ ∘ α⁻¹。
 Kelly 引理 ρ_{x ⨂ y} ≈ (id_x ⨂ ρ_y) ∘ α_{x,y,I}，此处通过 α⁻¹ 表述；[triangle_identity_left] 的右手伴随。
*)

Theorem triangle_identity_right {x y} :
  id ⨂ unit_right
    << x ⨂ (y ⨂ I) ~~> x ⨂ y >>
  unit_right ∘ tensor_assoc⁻¹.
Proof.
  pose proof (@bimap_unit_right_id x y I).
  normal.
  apply tensor_id_right_inj in X.
  assumption.
Qed.

(*
 [triangle_identity_right] solved for ρ across the forward associator:
 ρ ≈ (id ⨂ ρ) ∘ α. The α/α⁻¹ pair cancels, so this restates the previous
 lemma with α on the right rather than α⁻¹. 

 --------
 [triangle_identity_right] 在前向结合子中求解 ρ：
 ρ ≈ (id ⨂ ρ) ∘ α。α/α⁻¹ 对抵消，因此这用 α 在右侧而不是 α⁻¹ 重述了先前的引理。
*)

Theorem bimap_triangle_right {x y} :
  unit_right
    << (x ⨂ y) ⨂ I ~~> x ⨂ y >>
  bimap id unit_right ∘ to tensor_assoc.
Proof.
  rewrite triangle_identity_right.
  rewrite <- comp_assoc.
  rewrite iso_from_to; cat.
Qed.

(* The left companion of [bimap_triangle_right]: λ ≈ (λ ⨂ id) ∘ α⁻¹, i.e. [triangle_identity_left] solved for λ across the inverse associator. / [bimap_triangle_right] 的左伴随：λ ≈ (λ ⨂ id) ∘ α⁻¹，即 [triangle_identity_left] 在逆结合子上解 λ。 *)

Theorem bimap_triangle_left {x y} :
  unit_left
    << I ⨂ (x ⨂ y) ~~> x ⨂ y >>
  bimap unit_left id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

(*
 Kelly's lemma (Kelly 1964): the two unitors agree on the unit object,
 λ_I ≈ ρ_I : I ⨂ I ~> I. This is the canonical derived coherence fact, and
 it underlies, e.g., the commutativity of End(I) via Eckmann-Hilton. It is
 obtained here by combining the helper diagram [bimap_id_unit_left] at
 x = y = I with the triangle axiom and [id_unit_left], then cancelling the
 id[I]-tensorings on both sides. 

 --------
 凯利引理（Kelly 1964）：两个单位子在单位对象上是一致的，
 λ_I ≈ ρ_I : I ⨂ I ~> I。这是典型的导出相干性事实，
 并且它支撑了例如通过Eckmann-Hilton得到End(I)的交换性。这里通过将辅助图[bimap_id_unit_left]在 x = y = I时与三角公理和[id_unit_left]结合，然后在两边消去id [I]的张量操作而得到。
*)

Corollary unit_identity :
  to (@unit_left _ _ I) ≈ to (@unit_right _ _ I).
Proof.
  pose proof (@bimap_id_unit_left I I I).
  pose proof (@triangle_identity _ _ I I).
  normal.
  rewrite id_unit_left in X0.
  rewrite <- X0 in X; clear X0.
  apply tensor_id_left_inj in X.
  apply tensor_id_right_inj in X.
  apply X.
Qed.

End MonoidalProofs.
