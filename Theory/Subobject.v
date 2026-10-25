Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/subobject

   A subobject of an object x is (an equivalence class of) a monomorphism
   into x. Here the setoid structure itself carries the quotient: two monos
   into x are equivalent when there is an isomorphism of their domains
   commuting with them over x.

--------
nLab: https://ncatlab.org/nlab/show/subobject

   对象 x 的子对象 (subobject) 是进入 x 的单射（的等价类）。此处 setoid 结构本身
   承载商：两进入 x 的 mono 等价，当存在其定义域的同构且与它们在 x 上交换。
*)

Record SubObj {C : Category} (x : C) := {
  sub_dom : C;                     (* the domain of the mono / 单色的领域 *)
  sub_mono : sub_dom ~> x;         (* the mono into x / 将单色转换为 x *)
  sub_is_monic : Monic sub_mono
}.

Arguments sub_dom {C x} _.
Arguments sub_mono {C x} _.
Arguments sub_is_monic {C x} _.

#[export] Existing Instance sub_is_monic.

Section Subobject.

Universes o h p.
Context {C : Category@{o h p}}.
Context {x : C}.

#[export] Program Instance SubObj_Setoid : Setoid (SubObj x) := {
  equiv := fun u v =>
    { i : sub_dom u ≅ sub_dom v & sub_mono v ∘ to i ≈ sub_mono u }
}.
Next Obligation.
  constructor.
  - (* reflexivity: the identity isomorphism / 自反性：同一同构 *)
    intros u.
    exists iso_id; cat.
  - (* symmetry: the inverse triangle follows by precomposing with from i / 对称性：逆三角形通过与 i 预组合而得到 *)
    intros u v [i Hi].
    exists (iso_sym i); simpl.
    rewrite <- Hi.
    rewrite <- comp_assoc.
    rewrite iso_to_from; cat.
  - (* transitivity: compose the isomorphisms / 传递性：组成同构 *)
    intros u v w [i Hi] [j Hj].
    exists (iso_compose j i); simpl.
    rewrite comp_assoc.
    now rewrite Hj.
Qed.

(*
The preorder on subobjects: u ≤ v when the mono of u factors through the
   mono of v. The factorization is automatically monic ([sub_le_monic] below,
   Awodey §5.1) and unique ([sub_le_unique] below), so this is a genuine
   preorder whose induced equivalence is exactly the setoid equivalence
   above.

--------
子对象上的预序：当 u 的单态通过 v 的单态分解时，记 u ≤ v。这种分解自动是单态的（见下文 [sub_le_monic]，Awodey §5.1）并且是唯一的（见下文 [sub_le_unique]），因此这是一个真正的预序，其诱导的等价正好是上述的集合等价。
*)
Definition sub_le (u v : SubObj x) : Type :=
  { k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈ sub_mono u }.

Lemma sub_le_refl (u : SubObj x) : sub_le u u.
Proof.
  exists id; cat.
Defined.

Lemma sub_le_trans (u v w : SubObj x) :
  sub_le u v → sub_le v w → sub_le u w.
Proof.
  intros [k Hk] [l Hl].
  exists (l ∘ k).
  rewrite comp_assoc.
  now rewrite Hl.
Defined.

(*
Awodey, *Category Theory*, §5.1: a factorization BETWEEN subobjects is
   itself monic, so u ≤ v exhibits sub_dom u as a subobject of sub_dom v and
   not merely of x.  The file used to assert this in the header prose above
   with nothing in tree to back it.  The argument is the one [monic_cancel]
   packages -- sub_mono u is monic, and it factors as sub_mono v ∘ k -- but it
   is run inline here rather than by calling that lemma, because invoking it
   would need to rewrite under [Monic] along the factoring equation and the
   only ≈-transports for [Monic] in tree (Structure/Abelian.v,
   Structure/Regular/Factorization.v) are both downstream of this file.

--------
Awodey, *范畴论*, §5.1：子对象之间的一个分解本身是单射的，所以 u ≤ v 显示 sub_dom u 作为 sub_dom v 的子对象，而不仅仅是 x 的子对象。上述头部说明中使用该文件来断言此点，但在树中没有任何支持它的内容。论证是 [monic_cancel] 包所使用的——sub_mono u 是单射，并且它可以分解为 sub_mono v ∘ k——但这里是内联运行的，而不是调用那个引理，因为调用它需要根据分解方程在 [Monic] 下重写，并且树中 [Monic] 的唯一 ≈-传输（Structure/Abelian.v, Structure/Regular/Factorization.v）都在此文件的下游。
*)
Lemma sub_le_monic (u v : SubObj x) (H : sub_le u v) : Monic `1 H.
Proof.
  destruct H as [k Hk]; simpl.
  constructor; intros z g1 g2 Hg.
  apply (@monic _ _ _ (sub_mono u) (sub_is_monic u) z g1 g2).
  rewrite <- Hk, <- !comp_assoc.
  now rewrite Hg.
Qed.

(*
Mediating morphisms are unique: any two factorizations of sub_mono u
   through sub_mono v agree, by monicity of sub_mono v.

--------
中介态射是唯一的：通过子幺半群 v 的任何两个子幺半群 u 的分解都一致，这是由于子幺半群 v 的单射性。
*)
Lemma sub_le_unique (u v : SubObj x) (k k' : sub_dom u ~> sub_dom v) :
  sub_mono v ∘ k ≈ sub_mono u →
  sub_mono v ∘ k' ≈ sub_mono u →
  k ≈ k'.
Proof.
  intros Hk Hk'.
  apply (monic (Monic:=sub_is_monic v)).
  now rewrite Hk, Hk'.
Qed.

(*
Two subobjects are equivalent exactly when each factors through the other:
   the isomorphism supplies both factorizations, and conversely mutual
   factorizations k, l compose to endomorphisms over the same mono, hence to
   the identity by monicity, assembling an isomorphism of domains. Ends in
   Defined because both directions transport data.

--------
当且仅当每一个子对象都能通过另一个子对象进行分解时，两个子对象才是等价的：同构提供了这两种分解，反之，相互分解 k、l 组合在相同的单态上形成自同态，因此通过单态性得到恒等映射，从而组装出一个定义域的同构。由于两个方向都能传输数据，所以 Ends 有定义。
*)
Theorem sub_equiv_iff_mutual (u v : SubObj x) :
  (u ≈ v) ↔ (sub_le u v * sub_le v u).
Proof.
  split.
  - (* forward: to/from of the domain isomorphism are the factorizations / 正向：域同构的到/从是因式分解 *)
    intros [i Hi].
    split.
    + exists (to i); exact Hi.
    + exists (from i).
      rewrite <- Hi.
      rewrite <- comp_assoc.
      rewrite iso_to_from; cat.
  - (* backward: the round trips are id by monicity / 向后：往返由单调性识别 *)
    intros [[k Hk] [l Hl]].
    unshelve eexists {| to := k; from := l |}; simpl.
    + (* k ∘ l ≈ id, by monicity of sub_mono v / k ∘ l ≈ id，由 sub_mono v 的单性 *)
      apply (monic (Monic:=sub_is_monic v)).
      rewrite comp_assoc, Hk, Hl; cat.
    + (* l ∘ k ≈ id, by monicity of sub_mono u / l ∘ k ≈ id，由 sub_mono u 的单性 *)
      apply (monic (Monic:=sub_is_monic u)).
      rewrite comp_assoc, Hl, Hk; cat.
    + exact Hk.
Defined.

End Subobject.
