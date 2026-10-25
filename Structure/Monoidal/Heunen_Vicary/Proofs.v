Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.

Generalizable All Variables.

(*
 Derived equalities for the cartesian monoidal structure: a category whose
 tensor is the categorical product and whose unit is terminal.  In that
 setting all coherence data is forced by the universal property of products,
 and the lemmas below recover the projection/diagonal calculus from the
 abstract monoidal axioms.

 In this library the product UMP is not assumed directly; instead the
 cartesian monoidal structure is presented via a natural diagonal ∆x = ⟨id,
 id⟩ (Relevance) together with a counit `eliminate` x ~> I (Semicartesian),
 from which the projections are defined as

 proj_left  = unit_right ∘ id ⨂ eliminate : x ⨂ y ~> x,
 proj_right = unit_left  ∘ eliminate ⨂ id : x ⨂ y ~> y.

 The corollaries here are the cartesian shadows of the Fox-theorem composites
 ℓ ∘ (e ⨂ id) ∘ ∆ ≈ id and r ∘ (id ⨂ e) ∘ ∆ ≈ id: that ∆ is a (split, hence)
 monic copying map, that (id ⨂ e) ∘ ∆ and (e ⨂ id) ∘ ∆ are the inverse
 unitors ⟨id, e⟩ and ⟨e, id⟩, and that pairing the projections after ∆
 recovers the identity (and the braiding when crossed).

 nLab:      https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 These establish that the product's universal property is enough to derive the
 unitor, braiding, and diagonal facts of a symmetric monoidal category; here
 they are proven from the relevance/semicartesian axioms rather than assumed. 

 --------
 为笛卡尔单体结构导出的等式：一个范畴，其张量是范畴积且单位是终对象。在这种情况下，所有的相干性数据都由积的泛性质强制规定，下面的引理从抽象单体公理中恢复了投影/对角线的运算规则。

 在该库中，乘积的泛性质（UMP）并非直接假定；相反，笛卡尔单体结构是通过一个自然的对角线 ∆x = ⟨id, id⟩（相关性）以及一个余单位 `eliminate` x ~> I（半笛卡尔性）给出的，从中投影被定义为

 proj_left  = unit_right ∘ id ⨂ eliminate : x ⨂ y ~> x,
 proj_right = unit_left  ∘ eliminate ⨂ id : x ⨂ y ~> y。这里的推论是福克斯定理复合的笛卡尔影子
 ℓ ∘ (e ⨂ id) ∘ ∆ ≈ id 和 r ∘ (id ⨂ e) ∘ ∆ ≈ id：即 ∆ 是一个（可分裂的，因此是）单态拷贝映射，(id ⨂ e) ∘ ∆ 和 (e ⨂ id) ∘ ∆ 是逆单位子 ⟨id, e⟩ 和 ⟨e, id⟩，并且在 ∆ 后对投影进行配对可以恢复恒等映射（在交叉时也恢复交换映射）。

 nLab:       https://ncatlab.org/nlab/show/cartesian+monoidal+category 
 维基百科:  https://en.wikipedia.org/wiki/Cartesian_monoidal_category 

 这些建立了乘积的普遍性质足以推导对称幺半范畴的单位子、交换子和对角事实；这里它们是根据相关/半笛卡尔公理证明的，而不是假设的。
*)

Section CartesianMonoidal.

Context `{@CartesianMonoidal C}.

(*
 The right-handed Fox composite, generalized along f: discard the left copy,
 apply f to the right copy, then project with the left unitor.  Since the
 discarded factor is killed by `eliminate`, the result is just f.  Taking
 f = id recovers proj_right ∘ ∆ ≈ id (the comonoid counit law on the right). 

 --------
 右手 Fox 复合体，沿 f 广义化：丢弃左侧的副本，对右侧副本应用 f，然后用左单元器投影。由于被丢弃的因子被 `eliminate` 消掉，结果就是 f。取 f = id 可以恢复 proj_right ∘ ∆ ≈ id（右侧的余二态单位律）。
*)
Corollary unit_left_eliminate {x y} (f : x ~> y) :
  unit_left ∘ eliminate ⨂ f ∘ ∆x ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_right_diagonal.
  unfold proj_right.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural as X0; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(*
 The left-handed Fox composite, dual to unit_left_eliminate: apply f to the
 left copy, discard the right copy, then project with the right unitor.  With
 f = id this is proj_left ∘ ∆ ≈ id (the comonoid counit law on the left). 

 --------
 左手的 Fox 复合，与 unit_left_eliminate 对偶：将 f 应用于左边的副本，丢弃右边的副本，然后用右单元投影。 当 f = id 时，这就是 proj_left ∘ ∆ ≈ id（左侧的余单元律）。
*)
Corollary unit_right_eliminate {x y} (f : x ~> y) :
  unit_right ∘ f ⨂ eliminate ∘ ∆x ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_left_diagonal.
  unfold proj_left.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X.
  rewrite <- X; clear X.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

(*
 Copy x then delete the right factor: this is the pairing ⟨id, e⟩, which is
 exactly the inverse right unitor r⁻¹ in the product presentation. 

 --------
 复制 x 然后删除右因子：这就是配对 ⟨id, e⟩，它正好是乘积表示中的逆右单位元 r⁻¹。
*)
Lemma eliminate_right_diagonal {x} :
  id[x] ⨂ eliminate ∘ ∆x ≈ unit_right⁻¹.
Proof.
  apply (iso_to_monic unit_right).
  rewrite comp_assoc.
  rewrite unit_right_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

(* Dually, copy x then delete the left factor: the pairing ⟨e, id⟩, which is the inverse left unitor l⁻¹. / 同样地，复制 x 然后删除左因子：配对 ⟨e, id⟩，这是左单位元的逆 l⁻¹。 *)
Lemma eliminate_left_diagonal {x} :
  eliminate ⨂ id[x] ∘ ∆x ≈ unit_left⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite comp_assoc.
  rewrite unit_left_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

(*
 An associator-coherence step: copying the pair x ⨂ y and projecting the left
 factor of the first copy regroups (via the associator) to copying x alone.
 This is one of the two intermediate facts feeding proj_left_right_diagonal. 

 --------
 一个结合子-相干步骤：复制对 x ⨂ y 并投影第一份副本的左因子，通过结合子重组为仅复制 x。这是支撑 proj_left_right_diagonal 的两个中间事实之一。
*)
Lemma proj_left_id_diagonal {x y} :
  proj_left ⨂ id ∘ ∆(x ⨂ y) ≈ tensor_assoc ∘ ∆x ⨂ id.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ x _ id x _ id y _ eliminate y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_left, !id_right in X0.
  unfold proj_left.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  unfold braid2 in X0.
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- triangle_identity_left.
  normal.
  rewrite unit_left_braid.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  normal.
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

(*
 The companion associator-coherence step for the right projection: copying
 x ⨂ y and projecting the right factor of the first copy regroups, through a
 braiding, to copying y.  Feeds proj_right_left_diagonal. 

 --------
 右投影的伴随关联一致步骤：复制 x ⨂ y 并投影第一份拷贝的右因子，通过编织重组合并为复制 y。输入 proj_right_left_diagonal。
*)
Lemma proj_right_id_diagonal {x y} :
  proj_right ⨂ id ∘ ∆(x ⨂ y)
    ≈ tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ ∆y.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ x _ eliminate x _ id y _ id y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_right in X0.
  unfold braid2 in X0.
  unfold proj_right.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- to_unit_left_natural.
  rewrite <- !comp_assoc.
  repeat comp_left.
  rewrite comp_assoc.
  rewrite <- triangle_identity_left.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

(* Copy x ⨂ y, then keep the right factor of the first copy and the left factor of the second: this swaps the two components, i.e. it is the braiding σ_{x,y} = ⟨π₂, π₁⟩. / 复制 x ⨂ y，然后保留第一份复制的右因子和第二份复制的左因子：这样就交换了两个成分，即它是编织 σ_{x,y} = ⟨π₂, π₁⟩。 *)
Corollary proj_right_left_diagonal {x y} :
  proj_right ⨂ proj_left ∘ ∆(x ⨂ y) ≈ braid.
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_right_id_diagonal.
  unfold proj_left, proj_right.
  normal.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite triangle_identity_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to.
  normal.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite <- to_unit_right_natural.
  symmetry.
  rewrite <- id_right at 1.
  rewrite <- !comp_assoc.
  comp_left.
  symmetry.
  normal.
  spose (@from_tensor_assoc_natural _ _ x _ y _ y _ id id eliminate) as X0.
  rewrite bimap_id_id in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap _ _)).
  rewrites.
  normal.
  rewrite eliminate_right_diagonal.
  rewrite <- triangle_identity_right.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

(*
 Copy x ⨂ y, then keep the left factor of the first copy and the right factor
 of the second: the pairing ⟨π₁, π₂⟩ reassembles the original pair, so this is
 the identity.  This is the fork/projection round-trip law for the product. 

 --------
 复制 x ⨂ y，然后保留第一份复制的左因子和第二份的右因子：配对 ⟨π₁, π₂⟩ 重新组装原始对，因此这是恒等运算。这是乘积的叉/投影往返律。
*)
Corollary proj_left_right_diagonal {x y} :
  proj_left ⨂ proj_right ∘ ∆(x ⨂ y) ≈ id[x ⨂ y].
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_left_id_diagonal.
  rewrite comp_assoc.
  unfold proj_right.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite eliminate_right_diagonal.
  normal.
  rewrite <- triangle_identity.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

#[local] Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(*
 The diagonal is monic: it has a left inverse (proj_left ∘ ∆ ≈ id via
 unit_right_eliminate), so it is a split mono, hence monic.  The obligation
 cancels ∆ from ∆ ∘ g1 ≈ ∆ ∘ g2 using naturality of the diagonal. 

 --------
 对角线是单射的：它有一个左逆（proj_left ∘ ∆ ≈ id 通过 unit_right_eliminate），所以它是一个分裂单射，因此是单射的。这个要求使用对角线的自然性从 ∆ ∘ g1 ≈ ∆ ∘ g2 中消去 ∆。
*)
Program Instance diagonal_monic {x} :
  Monic ∆x.
Next Obligation.
  rewrite <- unit_left_eliminate.
  rewrite <- (unit_left_eliminate g2).
  rewrite <- (@eliminate_comp _ _ _ _ _ g1) at 1.
  rewrite <- (@eliminate_comp _ _ _ _ _ g2) at 1.
  rewrite <- (id_left g1) at 2.
  rewrite <- (id_left g2) at 2.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  srewrite diagonal_natural.
  rewrites.
  srewrite diagonal_natural.
  reflexivity.
Qed.

(* Projecting left after the braiding is the same as projecting right: swapping then taking π₁ equals taking π₂. / 在编织之后向左投影与向右投影是相同的：交换然后取 π₁ 等于取 π₂。 *)
Corollary proj_left_braid {x y} :
  proj_left ∘ braid ≈ @proj_right _ _ _ x y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_right_eliminate.
  reflexivity.
Qed.

(* Dually, projecting right after the braiding is projecting left. / 同样地，在编织之后向右投影就是向左投影。 *)
Corollary proj_right_braid {x y} :
  proj_right ∘ braid ≈ @proj_left _ _ _ x y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_left_eliminate.
  reflexivity.
Qed.

End CartesianMonoidal.
