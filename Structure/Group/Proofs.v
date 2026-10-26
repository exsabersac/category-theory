Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.

Generalizable All Variables.

(* * * Derived identities for group objects / * * 群对象的派生恒等式 *)

(*
 nLab:      https://ncatlab.org/nlab/show/group+object
 Wikipedia: https://en.wikipedia.org/wiki/Group_object

 A group object on [grp : C] (see [Structure.Group]) is a monoid object
 [(grp, mappend, mempty)] equipped with an inversion map [inverse : grp ~> grp]
 satisfying the two-sided inverse laws

 mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate   (left_inverse)
 mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate   (right_inverse)

 where ∆ is the cartesian diagonal and [eliminate] is the unique map to the
 tensor unit (terminal object). These are exactly the diagrammatic inverse
 axioms of the nLab/Wikipedia definition, with [mempty ∘ eliminate] playing
 the role of the constant map e ∘ p sending everything to the identity element.

 This file proves the two standard group facts that follow from those axioms,
 each carried out diagrammatically in an arbitrary cartesian monoidal category:

 - [left_inverse_unique]: uniqueness of (left) inverses — if
 [mappend ∘ f_inv ⨂ f ∘ ∆ X ≈ mempty ∘ eliminate], i.e. f_inv is a
 left inverse of f, then f_inv ≈ inverse[grp] ∘ f. This is the internal
 form of “yx = I implies y = x⁻¹”.

 - [mappend_inverse]: the inversion map is an anti-homomorphism,
 mappend ∘ inverse ⨂ inverse ≈ inverse ∘ mappend ∘ braid, i.e.
 a⁻¹·b⁻¹ = (b·a)⁻¹, the internal form of the classical (xy)⁻¹ = y⁻¹x⁻¹.
 Wikipedia/nLab do not spell these consequences out as separate diagrams;
 they are the standard derived group identities.

 The [CartesianMonoid] section first records two helper identities about a
 plain monoid object (collapsing a [mempty ∘ eliminate] half of a diagonal to
 the identity), which the group proofs reuse. Each lemma below is annotated
 with the ordinary-algebra calculation it mirrors. 

 --------
 nLab：https://ncatlab.org/nlab/show/group+object
 Wikipedia：https://en.wikipedia.org/wiki/Group_object

 在[grp : C]上的群对象（参见[Structure.Group]）是一个单子对象[(grp, mappend, mempty)]，配备有一个逆映射[inverse : grp ~> grp]，满足双边逆律：

 mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate（左逆）
 mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate（右逆）

 其中∆是笛卡尔对角映射，[eliminate]是到张量单位（终对象）的唯一映射。这正是nLab/Wikipedia定义中的图示逆公理，其中[mempty ∘ eliminate]起到将所有元素映射到单位元的常映射e ∘ p的作用。

 此文件证明了从这些公理出发的两个标准群事实，每个事实都在任意笛卡尔单体范畴中通过图示方式进行推导：- [left_inverse_unique]：左逆元的唯一性——如果 [mappend ∘ f_inv ⨂ f ∘ ∆ X ≈ mempty ∘ eliminate]，即 f_inv 是 f 的左逆元，那么 f_inv ≈ inverse [grp] ∘ f。这是“yx = I 蕴含 y = x⁻¹”的内部形式。

 - [mappend_inverse]：逆运算映射是一个反同态，mappend ∘ inverse ⨂ inverse ≈ inverse ∘ mappend ∘ braid，即 a⁻¹·b⁻¹ = (b·a)⁻¹，是经典恒等式 (xy)⁻¹ = y⁻¹x⁻¹ 的内部形式。维基百科/nLab 并未将这些结论单独列为图示；它们是标准的派生群恒等式。

 [CartesianMonoid] 部分首先记录了关于普通幺半群对象的两个辅助恒等式（将 [mempty ∘ eliminate] 对角线的一半折叠为单位元），群证明将其重复使用。下面的每个引理都标注了它所对应的常规代数计算。
*)

Section CartesianMonoid.

Context `{@CartesianMonoidal C}.
Context (mon : C).
Context `{@MonoidObject C _ grp}.

(*
 Multiplying an element on the right by the identity is the identity:
 g·I = g. Here the right factor of the diagonal is collapsed to [mempty]
 via [eliminate], then the right unit law [mempty_right] applies. 

 --------
 将一个元素在右侧与单位元素相乘就是该元素本身：
 g·I = g。这里对角线的右因子通过 [eliminate] 折叠为 [mempty]，然后应用右单位律 [mempty_right]。
*)
Lemma mempty_right_diagonal : mappend ∘ id ⨂ (mempty ∘ eliminate) ∘ ∆ grp ≈ id.
Proof.
  rewrite bimap_comp_id_left.
  rewrite comp_assoc.
  rewrite mempty_right.
  apply proj_left_diagonal.
Qed.

(*
 Multiplying an element on the left by the identity is the identity:
 I·g = g. Dual to [mempty_right_diagonal], using the left unit law
 [mempty_left]. 

 --------
 在左边将一个元素乘以单位元就是该元素本身：
 I·g = g。与 [mempty_right_diagonal] 对偶，使用左单位律
 [mempty_left] 。
*)
Lemma mempty_left_diagonal : mappend ∘ (mempty ∘ eliminate) ⨂ id ∘ ∆ grp ≈ id.
Proof.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite mempty_left.
  apply proj_right_diagonal.
Qed.

End CartesianMonoid.

Section GroupProofs.

Context `{@CartesianMonoidal C}.
Context (grp : C).
Context `{@GroupObject C _ grp}.

(*
 This proof is analogous to the following
 proof that y = x⁻¹ for an
 element y with yx = I:

 y = yI
 = y(xx⁻¹)
 = (yx)x⁻¹
 = Ix⁻¹
 = x⁻¹ 

 --------
 这个证明类似于以下证明：对一个元素 y，若 yx = I，则 y = x⁻¹：

 y = yI
 = y(xx⁻¹)
 = (yx)x⁻¹
 = Ix⁻¹
 = x⁻¹
*)
Lemma left_inverse_unique
  (X : C) (f : X ~> grp) (f_inv : X ~> grp)
  (f_left_inverse : mappend ∘ f_inv ⨂ f ∘ ∆ X ≈ mempty ∘ eliminate) :
  f_inv ≈ inverse[grp] ∘ f.
Proof.
  rewrite <- (id_left f_inv).
  (* ... = yI *)
  rewrite <- mempty_right_diagonal.
  rewrite <- (comp_assoc _ ∆grp f_inv).
  rewrite <- (diagonal_natural _ _ f_inv); simpl.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ (_ ⨂ _) (_ ⨂ _)).
  rewrite <- bimap_comp.
  rewrite <- (comp_assoc _ eliminate _).
  rewrite (unit_terminal (eliminate ∘ f_inv) (eliminate ∘ f)).
  rewrite !comp_assoc.
  (* ... = y(xx⁻¹) *)
  rewrite <- right_inverse.
  assert (mappend ∘ id ⨂ inverse[grp] ∘ ∆grp ∘ f ≈ mappend ∘ (id ⨂ inverse[grp] ∘ ∆grp ∘ f)) as R  by (rewrite comp_assoc; cat);
    rewrite R; clear R.
  rewrite bimap_comp.
  rewrite !comp_assoc.
  (* ... = (yx)x⁻¹ *)
  rewrite mappend_assoc_sym.
  rewrite <- (comp_assoc _ _ f).
  rewrite <- (diagonal_natural _ _ f); simpl.
  rewrite !comp_assoc.
  rewrite <- bimap_comp;
  rewrite id_left.
  rewrite <- (id_right f_inv).
  rewrite bimap_comp.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ (id ⨂ ∆X) (∆X)).
  rewrite diagonal_tensor_assoc.
  rewrite <- (comp_assoc tensor_assoc _ _);
  rewrite (comp_assoc _ tensor_assoc _);
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite iso_from_to;
  rewrite id_right.
  rewrite !comp_assoc;
  rewrite <- 2!(comp_assoc mappend _ _).
  rewrite <- 2!bimap_comp;
  rewrite id_right.
  rewrite !comp_assoc.
  (* ... = Ix⁻¹ *)
  rewrite f_left_inverse.
  rewrite (unit_terminal eliminate (eliminate ∘ (inverse[grp] ∘ f))).
  rewrite !comp_assoc;
  rewrite <- 2!(comp_assoc _ inverse[grp] f).
  rewrite bimap_comp.
  rewrite <- (comp_assoc _ _ ∆X).
  assert ((inverse[grp] ∘ f) ⨂ (inverse[grp] ∘ f) ≈ map (inverse[grp] ∘ f)) as R
    by reflexivity;
  rewrite R; clear R.
  rewrite <- (comp_assoc _ _ ∆X).
  rewrite (diagonal_natural _ _ (inverse[grp] ∘ f)).
  simpl.
  rewrite !comp_assoc.
  (* ... = x⁻¹ *)
  rewrite mempty_left_diagonal.
  cat.
Qed.

(*
 This proof is analogous to the following
 proof y⁻¹x⁻¹ = (xy)⁻¹: Calculate

 (y⁻¹x⁻¹)(xy) = y⁻¹(x⁻¹(xy))
 = y⁻¹((x⁻¹x)y)
 = y⁻¹(Iy)
 = y⁻¹y
 = I

 Then use the lemma above. 

 --------
 这个证明类似于下列证明 y⁻¹x⁻¹ = (xy)⁻¹：计算

 (y⁻¹x⁻¹)(xy) = y⁻¹(x⁻¹(xy))
 = y⁻¹((x⁻¹x)y)
 = y⁻¹(Iy)
 = y⁻¹y
 = I

 然后使用上面的引理。
*)
Lemma mappend_inverse : mappend ∘ inverse[grp] ⨂ inverse[grp] ≈ inverse[grp] ∘ mappend ∘ braid.
Proof.
  rewrite <- (comp_assoc inverse[grp] mappend braid).
  apply left_inverse_unique.
  (* (y⁻¹x⁻¹)(xy) = ... *)
  rewrite bimap_comp.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  (* ... = y⁻¹(x⁻¹(xy)) *)
  rewrite mappend_assoc.
  rewrite <- bimap_id_id.
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- to_tensor_assoc_natural.
  rewrite comp_assoc;
  rewrite <- (comp_assoc _ (id ⨂ mappend) _).
  rewrite <- bimap_comp;
  rewrite id_left.
  (* ... = y⁻¹((x⁻¹x)y) *)
  rewrite mappend_assoc_sym.
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- to_tensor_assoc_natural.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc mappend _ _).
  rewrite <- bimap_comp;
  rewrite id_left.
  rewrite diagonal_braid2.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ tensor_assoc (tensor_assoc ⁻¹)).
  rewrite iso_to_from;
  rewrite id_right.
  rewrite <- (comp_assoc _ (inverse[grp] ⨂ _) _).
  rewrite <- bimap_comp;
  rewrite id_right.
  rewrite hexagon_rotated.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ (inverse[grp] ⨂ braid) _).
  rewrite <- bimap_comp;
  rewrite id_right.
  rewrite braid_invol.
  rewrite <- bimap_id_id.
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ (tensor_assoc ⁻¹) _).
  rewrite iso_from_to;
  rewrite id_right.
  rewrite <- (bimap_id_left_right ∆grp ∆grp).
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ tensor_assoc _).
  rewrite <- bimap_id_id.
  rewrite <- to_tensor_assoc_natural.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc mappend (inverse[grp] ⨂ _) _).
  rewrite <- bimap_comp;
  rewrite id_right.
  rewrite <- (comp_assoc _ braid _).
  rewrite <- bimap_braid.
  rewrite !comp_assoc;
  rewrite <- (comp_assoc _ ((inverse[grp] ⨂ id) ⨂ id) _).
  rewrite <- bimap_comp;
  rewrite id_left.
  rewrite <- (comp_assoc _ (mappend ⨂ id) _).
  rewrite <- bimap_comp;
  rewrite id_left.
  rewrite !comp_assoc.
  (* ... = y⁻¹(Iy) *)
  rewrite left_inverse.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  (* ... = y⁻¹y *)
  rewrite mempty_left.
  rewrite <- (comp_assoc _ (eliminate ⨂ id) braid).
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite unit_left_braid.
  rewrite <- (id_left inverse[grp]).
  rewrite bimap_comp.
  rewrite comp_assoc;
  rewrite <- (comp_assoc _ _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  rewrite comp_assoc.
  rewrite triangle_identity_right.
  rewrite comp_assoc;
  rewrite <- (comp_assoc _ _ tensor_assoc).
  rewrite iso_from_to;
  rewrite id_right.
  rewrite <- (comp_assoc _ _ (∆grp ⨂ id[grp])).
  rewrite <- bimap_comp;
  rewrite id_right.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ unit_right _).
  rewrite <- to_unit_right_natural.
  rewrite !comp_assoc.
  (* ... = I *)
  rewrite left_inverse.
  rewrite <- !comp_assoc.
  rewrite eliminate_comp.
  reflexivity.
Qed.

End GroupProofs.
