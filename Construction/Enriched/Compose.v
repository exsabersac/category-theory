Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * Identity and composition of K-enriched functors, together with the left
   and right whiskering of a V-natural transformation by an enriched functor.

   These assemble the categorical structure on K-categories: EnrichedId and
   EnrichedCompose give the identity and composite 1-cells, while the two
   whiskerings supply the horizontal action of 1-cells on V-natural 2-cells
   that Fun.v needs to build the enriched functor category. 

   --------
   * K-增强函子的恒等和组合，以及由增强函子对 V-自然变换进行的左鞭挞和右鞭挞。

   这些构成了 K-范畴上的范畴结构：EnrichedId 和 EnrichedCompose 提供了恒等 1-箭头和复合 1-箭头，而这两种鞭挞为 1-箭头对 V-自然 2-箭头的水平作用提供了支持，这是 Fun.v 构建增强函子范畴所需要的。
*)

(*
   * The identity enriched functor: the object map is the identity and each
   hom-object map is the identity K-morphism id[x ⟿ y]. 

   --------
   * 恒等增强函子：对象映射是恒等映射，每个同态对象映射是恒等 K-态射 id [x ⟿ y] 。
*)

Program Definition EnrichedId {K : Category} `{@Monoidal K}
        (C : Enriched K) : EnrichedFunctor K C C := {|
  efobj := fun x => x;
  efmap := fun x y => id
|}.
Next Obligation.
  (* preserves identity: id ∘ eid ≈ eid, by id_left / 保持身份：id ∘ eid ≈ eid，根据 id_left *)
  intros.
  simpl.
  now rewrite id_left.
Qed.
Next Obligation.
  (*
 preserves composition: ecompose ∘ id ⨂ id ≈ id ∘ ecompose.
 bimap id id ≈ id collapses the left tensor, id_left the right. 

 --------
 保留组合：ecompose ∘ id ⨂ id ≈ id ∘ ecompose。
 bimap id id ≈ id 折叠左张量，id_left 折叠右张量。
*)
  intros.
  simpl.
  rewrite bimap_id_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
   * Composition of enriched functors G ∘ F: compose object maps and compose
   the hom-object maps in K. 

   --------
   * 富函子 G ∘ F 的复合：复合对象映射并复合 K 中的 Hom 对象映射。
*)

Program Definition EnrichedCompose {K : Category} `{@Monoidal K}
        {C D E : Enriched K}
        (G : EnrichedFunctor K D E) (F : EnrichedFunctor K C D) :
  EnrichedFunctor K C E := {|
  efobj := fun x => efobj (efobj x);
  efmap := fun x y => efmap ∘ efmap
|}.
Next Obligation.
  (*
 preserves identity: (efmap G ∘ efmap F) ∘ eid ≈ eid.
 Reassociate, apply F.efmap_id then G.efmap_id. 

 --------
 保持身份： (efmap G ∘ efmap F) ∘ eid ≈ eid。重新关联，应用 F.efmap_id 然后 G.efmap_id。
*)
  intros.
  simpl.
  rewrite <- comp_assoc.
  rewrite (efmap_id (EnrichedFunctor := F)).
  rewrite (efmap_id (EnrichedFunctor := G)).
  reflexivity.
Qed.
Next Obligation.
  (*
 preserves composition:
 ecompose ∘ (efmap G ∘ efmap F) ⨂ (efmap G ∘ efmap F)
 ≈ (efmap G ∘ efmap F) ∘ ecompose.
 Split the tensor with bimap_comp, then use G.efmap_comp and
 F.efmap_comp. 

 --------
 保持组合：
 ecompose ∘ (efmap G ∘ efmap F) ⨂ (efmap G ∘ efmap F)
 ≈ (efmap G ∘ efmap F) ∘ ecompose。
 使用 bimap_comp 分裂张量，然后使用 G.efmap_comp 和 F.efmap_comp。
*)
  intros.
  simpl.
  rewrite bimap_comp.
  rewrite comp_assoc.
  rewrite (efmap_comp (EnrichedFunctor := G)).
  rewrite <- comp_assoc.
  rewrite (efmap_comp (EnrichedFunctor := F)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(*
   * Left whiskering: given a V-natural transformation σ : F ⟹ G between
   F, G : C ⟶ D and an enriched functor H : D ⟶ E, produce a V-natural
   transformation H∘F ⟹ H∘G whose component at x is efmap H ∘ σ_x. 

   --------
   * 左鞭打：给定一个 V-自然变换 σ : F ⟹ G，其中 F, G : C ⟶ D，并且给定一个富集函子 H : D ⟶ E，构造一个 V-自然变换 H∘F ⟹ H∘G，其在 x 处的分量为 efmap H ∘ σ_x。
*)

Program Definition EnrichedWhiskerLeft {K : Category} `{@Monoidal K}
        {C D E : Enriched K}
        {F G : EnrichedFunctor K C D}
        (H : EnrichedFunctor K D E)
        (σ : EnrichedTransform F G) :
  EnrichedTransform (EnrichedCompose H F) (EnrichedCompose H G) := {|
  etransform := fun x => efmap ∘ etransform x
|}.
Next Obligation.
  (*
 enaturality of the left whisker at x, y.
 LHS:  ecompose ∘ ((efmap H ∘ σ_y) ⨂ (efmap H ∘ efmap F)) ∘ unit_left⁻¹
 Split the tensor, pull ecompose ∘ (efmap H ⨂ efmap H) through
 H.efmap_comp, then apply σ's enaturality, and reassemble the RHS. 

 --------
 左边须在 x, y 处的不自然性。
 左边:  ecompose ∘ ((efmap H ∘ σ_y) ⨂ (efmap H ∘ efmap F)) ∘ unit_left⁻¹
 拆分张量，通过 H.efmap_comp 提出 ecompose ∘ (efmap H ⨂ efmap H)，然后应用 σ 的不自然性，再重新组合右边。
*)
  intros.
  simpl.
  (* split each tensor of composites into a composite of tensors / 将复合张量的每个张量拆分为张量的复合 *)
  rewrite !bimap_comp.
  (*
 expose ecompose ∘ (efmap H ⨂ efmap H) on both sides and collapse it
 through H.efmap_comp into efmap H ∘ ecompose 

 --------
 在两边施加 expose ecompose ∘ (efmap H ⨂ efmap H)，并通过 H.efmap_comp 将其折叠成 efmap H ∘ ecompose
*)
  rewrite !comp_assoc.
  rewrite !(efmap_comp (EnrichedFunctor := H)).
  (*
 factor efmap H off the far left and finish by σ's enaturality 

 --------
 将 efmap H 从最左边提出，并以 σ 的自然性结束
*)
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite !comp_assoc.
  apply (enaturality (EnrichedTransform := σ)).
Qed.

(*
   * Right whiskering: given σ : F ⟹ G between F, G : C ⟶ D and an enriched
   functor H : B ⟶ C, produce F∘H ⟹ G∘H whose component at x is σ_{H x}. 

   --------
   * 右打毛：给定 σ : F ⟹ G，F, G : C ⟶ D 以及一个增强函子 H : B ⟶ C，产生 F∘H ⟹ G∘H，其在 x 的分量为 σ_{H x}。
*)

Program Definition EnrichedWhiskerRight {K : Category} `{@Monoidal K}
        {B C D : Enriched K}
        {F G : EnrichedFunctor K C D}
        (H : EnrichedFunctor K B C)
        (σ : EnrichedTransform F G) :
  EnrichedTransform (EnrichedCompose F H) (EnrichedCompose G H) := {|
  etransform := fun x => etransform (efobj x)
|}.
Next Obligation.
  (*
 enaturality of the right whisker at x, y.
 LHS:  ecompose ∘ (σ_{Hy} ⨂ (efmap F ∘ efmap H)) ∘ unit_left⁻¹
 Split the tensor: (id ⨂ efmap H) ∘ unit_left⁻¹ ≈ unit_left⁻¹ ∘ efmap H
 by from_unit_left_natural; then apply σ's enaturality, and turn the
 RHS coercion back with from_unit_right_natural. 

 --------
 在 x, y 处右须的非自然性。
 左侧:  ecompose ∘ (σ_{Hy} ⨂ (efmap F ∘ efmap H)) ∘ unit_left⁻¹
 分解张量: (id ⨂ efmap H) ∘ unit_left⁻¹ ≈ unit_left⁻¹ ∘ efmap H
 由 from_unit_left_natural 得到; 然后应用 σ 的非自然性，并通过 from_unit_right_natural 将右侧的强制转换恢复回来。
*)
  intros.
  simpl.
  (*
 pad each component transform with an identity so the tensor becomes a
 tensor of composites, then split it 

 --------
 在每个分量变换中填充恒等元，使张量成为
 复合张量，然后将其拆分
*)
  rewrite <- (id_right (etransform (efobj y))).
  rewrite <- (id_right (etransform (efobj x))).
  rewrite !bimap_comp.
  (*
 right-associate so bimap id (efmap H) ∘ unit_left⁻¹ and
 bimap (efmap H) id ∘ unit_right⁻¹ appear as bare subterms, then slide
 the unitors past efmap H 

 --------
 右结合，因此 bimap id (efmap H) ∘ unit_left⁻¹ 和 bimap (efmap H) id ∘ unit_right⁻¹ 出现在裸子项中，然后将单位元器绕过 efmap H 移动
*)
  rewrite <- !comp_assoc.
  rewrite from_unit_left_natural.
  rewrite from_unit_right_natural.
  (*
 factor efmap H off the far right and finish by σ's enaturality 

 --------
 将 efmap H 从最右边提出，并以 σ 的自然性结束
*)
  rewrite !comp_assoc.
  apply compose_respects; [ | reflexivity ].
  apply (enaturality (EnrichedTransform := σ)).
Qed.
