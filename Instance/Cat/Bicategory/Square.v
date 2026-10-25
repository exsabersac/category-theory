Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Square.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Adjunction.

Generalizable All Variables.

(* * * The adjoint-square mate is the mates mate, at Cat / * * 伴随平方将死是将死中的将死，在 Cat *)

(*
 nLab: https://ncatlab.org/nlab/show/mate

 Adjunction/Square.v develops Mac Lane §IV.7 Exercises 4 and 5 in
 ordinary-category vocabulary, with no bicategorical machinery, so that
 it applies to categories of any size.  This file reconciles that
 development with Theory/Bicategory/Mates.v's [mate] and
 [mate_inv] read in Cat, of which it is the ordinary-functor case, and
 it is the sibling of Instance/Cat/Bicategory/Conjugate.v, which does
 the same for the identity-bounding-cell development of
 Adjunction/Conjugate.v.

 Nothing here needs a padding transformation.  Scout measurement, re-run
 here: [mate] and [mate_inv] at Cat take and return the ORDINARY functor
 composites — the statements below ascribe [SqMate A A' K L sg] against
 [mate SqBA SqBA' sg] with no comparison map and no transport — because
 the bounding cells are genuine functors K and L rather than identities,
 so the F' ◯ Id trap that Instance/Cat/Bicategory/Conjugate.v records
 does not arise on this route.  The bridge to the bicategorical side is
 taken through the TRANSPARENT Instance/Cat/Bicategory/Adjunction.v
 [Cat_Adjunction_BicatAdjunction], never through that file's
 [Cat_BicatAdjunction_Adjunction_iff], which is data closed with Qed.

 WHAT THE COMPARISON COSTS, MEASURED.  After [simpl; unfold sq_mate] the
 right-hand side of [sq_mate_is_mate] carries NINE unitor and associator
 residues of the form [fmap _ id] (counted in the printed goal: three
 [fmap[U'] (fmap[K] id)], three [fmap[U'] id], two [fmap[L] id] and one
 [fmap[L] (fmap[U] id)]), against the intended
 [fmap[U'] (fmap[K] counit) ∘ (fmap[U'] (sg (U a)) ∘ unit)].  They are
 cleared by exactly [rewrite !fmap_id; rewrite ?id_left, ?id_right],
 which is what Instance/Cat/Bicategory/Adjunction.v
 [Cat_mate_unfold_raw] does; the extra steps on this side are
 [to_adj_unit], which turns the caller's own transpose into the pasted
 form, then one [fmap_comp] and one [comp_assoc] to reassociate it.
 The strict form [SqMate A A' K L sg a = mate SqBA SqBA' sg a] is
 REFUTED at [eq_refl] (pinned as Test/ProbeSquare398.v's N12); only ≈
 holds.  [sq_mate_inv_is_mate_inv] goes
 through the same way and is in fact shorter — [from_adj_counit] then
 the same two clearing lines, with no [fmap_comp] and no [comp_assoc] —
 and its goal carries nine residues of the same shape.

 [adjoint_square_iff_Cat_mate] is the issue's second work item read at
 Cat: the adjoint-square condition on a pair of natural transformations
 holds exactly when the second is the bicategorical mate of the first.
 It is stated with NO naturality hypothesis, which is stronger than the
 corresponding bare-family statement [adjoint_square_iff_mate] needs:
 the σ here is a [Transform], so Adjunction/Square.v's
 [transform_SigmaNat] supplies the hypothesis for free.
 [adjoint_square_iff_Cat_mate_inv] is its mirror over [mate_inv], from
 [transform_TauNat].

 NOT DELIVERED.  Nothing relates the two PASTINGS of
 Adjunction/Square.v to any bicategorical composition, so
 Theory/Bicategory/Mates.v's descope ledger 10 — pasting functoriality
 in an ARBITRARY bicategory — was left untouched by this file, which did
 not edit Mates.v; Instance/Adj/Bicategory.v (#399) later narrows that
 note without discharging the entry, and its arbitrary-bicategory half
 remains open.
 No comparison with Mates.v's [mate_iso] as an isomorphism of setoids, so
 Adjunction/Square.v's [square_bijection] is not identified with it.  No
 [mate_inv] component lemma is added to the donor file.  Nothing is
 registered as an [Instance], and there is no concrete witness. 

 --------
 nLab: https://ncatlab.org/nlab/show/mate

 Adjunction/Square.v 使用普通类别的词汇展开了 Mac Lane §IV.7 练习 4 和 5，不涉及双范畴的工具，因此适用于任何大小的范畴。该文件将这一发展与 Theory/Bicategory/Mates.v 中在 Cat 中读取的 [mate] 和 [mate_inv] 进行了协调，这些是普通函子情况下的对应版本，并且它是 Instance/Cat/Bicategory/Conjugate.v 的姊妹文件，后者对 Adjunction/Conjugate.v 中关于单位边界单元的展开做了相同处理。这里没有任何需要填充转换的地方。在此重新运行侦测测量：[mate] 和 [mate_inv] 在 Cat 中获取并返回普通函子复合——下面的语句将 [SqMate A A' K L sg] 指派给 [mate SqBA SqBA' sg]，没有比较映射也没有传输——因为边界单元是真正的函子 K 和 L 而不是恒等映射，所以 Instance/Cat/Bicategory/Conjugate.v 记录的 F' ◯ Id 陷阱在这条路径上不会出现。通向双范畴侧的桥梁是通过透明的 Instance/Cat/Bicategory/Adjunction.v [Cat_Adjunction_BicatAdjunction]，而从不通过该文件的 [Cat_BicatAdjunction_Adjunction_iff]，该文件的数据用 Qed 封闭。比较的成本是什么，已被衡量。在 [simpl; unfold sq_mate] 之后，[sq_mate_is_mate] 的右边包含九个单位子和结合子残余，形式为 [fmap _ id]（在打印目标中计数：三个 [fmap[U']（fmap [K] id）]，三个 [fmap[U'] id]，两个 [fmap[L] id]，以及一个 [fmap[L]（fmap [U] id）]），对比预期的 [fmap[U']（fmap [K] counit）∘（fmap [U']（sg（U a））∘ unit）。它们正好被 [rewrite !fmap_id; rewrite ?id_left, ?id_right] 清除，这正是 Instance/Cat/Bicategory/Adjunction.v [Cat_mate_unfold_raw] 所做的；此侧的额外步骤是 [to_adj_unit]，它将调用者自己的转置转换为粘贴形式，然后一个 [fmap_comp] 和一个 [comp_assoc] 重新关联它。严格形式 [SqMate A A' K L sg a = mate SqBA SqBA' sg a] 在 [eq_refl] 被反驳（固定为 Test/ProbeSquare398.v 的 N12）；只有 ≈ 成立。[sq_mate_inv_is_mate_inv] 以相同的方式进行，实际上更短——[from_adj_counit] 然后是相同的两条清理线，没有 [fmap_comp]，也没有 [comp_assoc]——其目标包含九个相同形状的残基。

 [adjoint_square_iff_Cat_mate] 是该问题的第二个工作项，在 Cat 中读取：一对自然变换上的伴随平方条件仅当第二个是第一个的双范畴配偶时成立。它以没有自然性假设的方式陈述，这比相应的裸族陈述 [adjoint_square_iff_mate] 所需要的更强：这里的 σ 是一个 [Transform]，因此 Adjunction/Square.v 的 [transform_SigmaNat] 自动提供了假设。[adjoint_square_iff_Cat_mate_inv] 是它在 [mate_inv] 上的镜像，来自 [transform_TauNat]。未交付。没有任何内容将两个 Adjunction/Square.v 的粘贴与任何双范畴组合联系起来，因此 Theory/Bicategory/Mates.v 的去作用账本 10 — 在任意双范畴中的粘贴函子性 — 没有被此文件触及，该文件也未编辑 Mates.v；Instance/Adj/Bicategory.v (#399) 后来缩小了该说明但未清除条目，其任意双范畴的部分仍然开放。没有将 Mates.v 的 [mate_iso] 作为集合同构进行比较，因此 Adjunction/Square.v 的 [square_bijection] 并未与其对应。没有向供体文件添加 [mate_inv] 组件引理。没有任何内容被注册为 [Instance]，也没有具体的实例证据。
*)

Section SquareMatesAtCat.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Definition SqBA  : BicatAdjunction (B:=Cat_Bicategory) F  U  :=
  Cat_Adjunction_BicatAdjunction A.
Definition SqBA' : BicatAdjunction (B:=Cat_Bicategory) F' U' :=
  Cat_Adjunction_BicatAdjunction A'.

Theorem sq_mate_is_mate (sg : F' ◯ L ⟹ K ◯ F) :
  SqMate A A' K L sg ≈ mate SqBA SqBA' sg.
Proof.
  intros a; simpl; unfold sq_mate.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem sq_mate_inv_is_mate_inv (ta : L ◯ U ⟹ U' ◯ K) :
  SqMateInv A A' K L ta ≈ mate_inv SqBA SqBA' ta.
Proof.
  intros x; simpl; unfold sq_mate_inv.
  rewrite (from_adj_counit (H:=A')).
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem adjoint_square_iff_Cat_mate
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT A A' K L sg ta ↔ ta ≈ mate SqBA SqBA' sg.
Proof.
  split; intro H.
  - intro a.
    rewrite (SqMate_uniq A A' K L sg ta H a).
    exact (sq_mate_is_mate sg a).
  - apply (sq_mate_to_hom A A' K L _ _ (transform_SigmaNat K L sg)).
    intro a.
    rewrite (H a).
    symmetry; exact (sq_mate_is_mate sg a).
Qed.

Theorem adjoint_square_iff_Cat_mate_inv
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT A A' K L sg ta ↔ sg ≈ mate_inv SqBA SqBA' ta.
Proof.
  split; intro H.
  - intro x.
    rewrite (SqMateInv_uniq A A' K L sg ta H x).
    exact (sq_mate_inv_is_mate_inv ta x).
  - apply (sq_mate_inv_to_hom A A' K L _ _ (transform_TauNat K L ta)).
    intro x.
    rewrite (H x).
    symmetry; exact (sq_mate_inv_is_mate_inv ta x).
Qed.

End SquareMatesAtCat.
