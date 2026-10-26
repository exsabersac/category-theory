Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

(* * * Grp is well-powered one universe up / * * Grp 是一个动力充足的宇宙提升 *)

(*
 nLab:      https://ncatlab.org/nlab/show/well-powered+category
 Wikipedia: https://en.wikipedia.org/wiki/Subgroup

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.8, book p. 130 (PDF p. 139): a category is well-powered when the
 subobjects of each object form a small set.  In [Grp] a subobject is a
 subgroup up to isomorphism, so the classical index is the set of
 subgroups.  This file states that at Structure/WellPowered.v's per-object
 record: [Grp_WellPoweredAt_up G : WellPoweredAt G], with index
 [Subgroup G] (Instance/Grp/Quotient.v).  The [Sets] witnesses are
 Instance/Sets/WellPowered.v.

 WHAT IS BUILT.  [wp_to] sends a subgroup to its inclusion
 ([grp_sub_of_subgroup], from Instance/Grp/Quotient.v's [SubgroupGrp],
 [sub_incl] and [sub_incl_monic]); [wp_from] sends a subobject to the
 image of its mono ([grp_image_subgroup], whose membership is Instance/
 Grp/Epi.v's [Type]-valued [GrpImage] and whose closure laws are that
 file's [GrpImage_respects], [GrpImage_unit], [GrpImage_mul] and
 [GrpImage_inv]).  The domain isomorphism [grp_image_iso] projects the
 carried preimage one way and pairs an element with itself the other.
 Nothing is assumed.

 A TRAP, recorded.  The [GrpImage_*] closure lemmas are [Qed], so the
 preimages they build cannot be computed with.  The homomorphism laws of
 the forward map [grp_image_fwd] are therefore proved through
 injectivity of the mono (Instance/Grp.v's [Grp_injectivity_is_monic])
 and [projT2] of the opaque witnesses, never by unfolding them.

 WHY ONE UNIVERSE UP, measured.  [Subgroup G] has a [Type]-valued
 membership predicate on the carrier, so it sits one universe above the
 carrier, which is [Grp]'s hom universe:

 Grp_WellPoweredAt_up@{u u0 u1} :
 ∀ G : obj[Grp@{u0 u1}], WellPoweredAt@{u u0 u0 u1 u} G
 ( * Set < u0, u1 < u, u1 < u0 * )

 ([WellPoweredAt]'s first slot is the index universe, its fourth the hom
 universe.)  At Structure/WellPowered.v's pin the witness is refused, in
 a copy of this whole file with the one command appended:
 [WellPowered@{o h h o o} Grp@{o h}] with [h < o] gives “The term
 ”Grp_WellPoweredAt_up G“ has type ”WellPoweredAt@{R5.4103 o o h
 R5.4103} G“ while it is expected to have type ”WellPoweredAt@{h o o h o}
 G“ (universe inconsistency: Cannot enforce o = h because h < o)”, and
 the control [Grp_WellPoweredAt_up@{o o h} G] is accepted.  [Set < u0]
 and [u1 < u0] are inherited, not introduced here: [About Grp] reads
 [Grp@{u p} : Category@{u p p}] with [Set < u] and [p < u], the [Set+1]
 that the [PropEquiv] field puts in [GrpObject]'s sort (CLAUDE.md's
 universe section).

 MEASUREMENTS.  7 [.glob] heads ('^(def|prf|thm|ind|constr|proj|rec) ')
 and 6 [Program] obligations ([grp_image_fwd_obligation_1] to [_3] and
 [grp_image_bwd_obligation_1] to [_3], found by [strings] on the .vo):
 all 13 report “Closed under the global context” by their fully
 qualified names.  [grp_image_iso] and [grp_image_to_from] are
 [Defined] (an isomorphism and a ≈ of subobjects, both data); the six
 obligations are [Qed].

 NOT DELIVERED.  [Grp] well-powered at the pin, unconditionally or under
 any hypothesis: a [Prop]-valued membership would sit at the carrier
 universe but meets the refusal Instance/Sets/WellPowered.v quotes for
 [Sets], and nothing is attempted here.  [Grp] co-well-powered: Instance/
 Grp/QuotObj.v's header records that its surjectivity leg takes the
 double-negation stability of image membership as a hypothesis, and no
 index of quotients is built.  No [Ab] analogue.  An earlier revision
 said “No [Ab] or [RMod R] analogue”; since #454 Instance/Mod/
 WellPowered.v is the [RMod R] one: [RMod_WellPoweredAt_up] and
 [RMod_CoWellPoweredAt_up] one universe up, and
 [RMod_WellPowered_untruncate] and [RMod_CoWellPowered_untruncate] at
 the pin under [Untruncate]. 

 --------
 nLab：https://ncatlab.org/nlab/show/well-powered+category
 Wikipedia：https://en.wikipedia.org/wiki/Subgroup

 Mac Lane，《给工作中的数学家的范畴》，第2版（GTM 5），§V.8，第130页（PDF第139页）：当每个对象的子对象形成一个小集合时，范畴是良幂的。在[Grp]中，子对象是按同构的子群，因此经典指标是子群集合。该文件在Structure/WellPowered.v的每对象记录中声明：[Grp_WellPoweredAt_up G : WellPoweredAt G]，具有指标[Subgroup G]（Instance/Grp/Quotient.v）。[Sets]的见证位于Instance/Sets/WellPowered.v。什么已建立。[wp_to] 发送一个子群到它的包含（[grp_sub_of_subgroup]，来自 Instance/Grp/Quotient.v 的 [SubgroupGrp]、[sub_incl] 和 [sub_incl_monic]）；[wp_from] 发送一个子对象到它的单态像（[grp_image_subgroup]，其成员是 Instance/Grp/Epi.v 的 [Type] 值的 [GrpImage]，并且其闭包律是该文件的 [GrpImage_respects]、[GrpImage_unit]、[GrpImage_mul] 和 [GrpImage_inv]）。域同构 [grp_image_iso] 将所携带的前像投影到一边，并将一个元素与自身配对到另一边。没有假设。一个陷阱，已记录。[GrpImage_*] 闭包引理是 [Qed]，因此它们构建的原像无法被计算。前向映射 [grp_image_fwd] 的同态律因此通过单态（Instance/Grp.v 的 [Grp_injectivity_is_monic]）的单射性以及不透明证人的 [projT2] 得到证明，从不通过展开它们。

 为什么是一个宇宙层上升，已测量。[Subgroup G] 在载体上有一个 [Type] 值的隶属谓词，因此它位于载体之上的一个宇宙层，而载体是 [Grp] 的同态宇宙：

 Grp_WellPoweredAt_up@{u u0 u1} ：
 ∀ G : obj [Grp@{u0 u1}] ， WellPoweredAt@{u u0 u0 u1 u} G
 ( * Set < u0, u1 < u, u1 < u0 * )([WellPoweredAt] 的第一个插槽是索引宇宙，第四个是 homo 宇宙。) 在 Structure/WellPowered.v 的引脚处，见证被拒绝，在附加了一个命令的整个文件副本中：
 [WellPowered@{o h h o o} Grp@{o h}] 与 [h < o] 给出 “术语 'Grp_WellPoweredAt_up G' 的类型是 'WellPoweredAt@{R5.4103 o o h R5.4103} G'，而期望类型是 'WellPoweredAt@{h o o h o} G'（宇宙不一致：无法强制 o = h，因为 h < o）”，并且控制 [Grp_WellPoweredAt_up@{o o h} G] 被接受。[Set < u0] 和 [u1 < u0] 是继承的，而不是这里引入的：[About Grp] 读取 [Grp@{u p} : Category@{u p p}] 与 [Set < u] 和 [p < u]，[Set+1] 即 [PropEquiv] 字段在 [GrpObject] 的类型中放入（CLAUDE.md 的宇宙部分）。测量。7 个 [.glob] 头 ('^(def|prf|thm|ind|constr|proj|rec)') 和 6 个 [Program] 义务（[grp_image_fwd_obligation_1] 到 [_3] 和 [grp_image_bwd_obligation_1] 到 [_3]，由 [strings] 在 .vo 中发现）：所有 13 个通过它们的完全限定名称报告“在全局上下文下关闭”。[grp_image_iso] 和 [grp_image_to_from] 是 [Defined]（一个同构和子对象的 ≈，两者都是数据）；六个义务是 [Qed]。未交付。[Grp] 在针脚处是良好强大的，无条件或在任何假设下：[Prop] 值的成员将位于承载宇宙中，但符合 Instance/Sets/WellPowered.v 对 [Sets] 的拒绝引用，这里没有尝试。[Grp] 共良好强大：Instance/Grp/QuotObj.v 的头部记录其满射性腿将图像成员的双重否定稳定性作为假设，并且没有构建商的索引。没有 [Ab] 的对应物。早期版本曾说“没有 [Ab] 或 [RMod R] 的对应物”；由于 #454 Instance/Mod/WellPowered.v 是 [RMod R] 的一个：[RMod_WellPoweredAt_up] 和 [RMod_CoWellPoweredAt_up] 上一个宇宙，以及 [RMod_WellPowered_untruncate] 和 [RMod_CoWellPowered_untruncate] 在针脚下的 [Untruncate] 。
*)

(*
 The image of a homomorphism as a [Subgroup]; its membership is
 Instance/Grp/Epi.v's [GrpImage], a [Type]-valued “has a preimage”. 

 --------
 同态的像作为 [Subgroup]；它的成员是 Instance/Grp/Epi.v 的 [GrpImage] ，一个取值为 [Type] 的“有原像”的元素。
*)
Definition grp_image_subgroup {G H : Grp} (f : G ~{Grp}~> H) : Subgroup H :=
  {| sub_mem  := GrpImage f ;
     sub_resp := GrpImage_respects f ;
     sub_unit := GrpImage_unit f ;
     sub_mul  := GrpImage_mul f ;
     sub_inv  := GrpImage_inv f |}.

(* The subobject a subgroup names: its inclusion. / 子对象一个子群命名：它的包含。 *)
Definition grp_sub_of_subgroup (G : Grp) (S : Subgroup G) : SubObj G :=
  @Build_SubObj Grp G (SubgroupGrp S) (sub_incl S) (sub_incl_monic S).

Section GrpToFrom.

Context (G : Grp) (u : SubObj G).

(*
 The domain isomorphism between the image of the mono and its domain.
 The closure lemmas of Instance/Grp/Epi.v are [Qed], so the homomorphism
 laws of the forward map are proved through injectivity of the mono, never
 by computing the opaque witnesses. 

 --------
 单射的像与其定义域之间的域同构。
 Instance/Grp/Epi.v 的闭包引理是 [Qed]，因此前向映射的同态律是通过单射的单射性来证明的，而不是通过计算不透明的见证。
*)
Program Definition grp_image_fwd :
  SubgroupGrp (grp_image_subgroup (sub_mono u)) ~{Grp}~> sub_dom u := {|
  grp_map := {| morphism := fun p => `1 (`2 p) |}
|}.
Next Obligation.
  intros [b [a Ha]] [b' [a' Ha']] H; simpl in *.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite Ha, Ha'. exact H.
Qed.
Next Obligation.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite (projT2 (GrpImage_unit (sub_mono u))).
  symmetry. apply (grp_map_unit (sub_mono u)).
Qed.
Next Obligation.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite (grp_map_mul (sub_mono u)).
  rewrite (projT2 (GrpImage_mul (sub_mono u) _ _ (projT2 a) (projT2 b))).
  destruct a as [b1 [x Hx]], b as [b2 [y Hy]]; simpl.
  rewrite Hx, Hy. reflexivity.
Qed.

Program Definition grp_image_bwd :
  sub_dom u ~{Grp}~> SubgroupGrp (grp_image_subgroup (sub_mono u)) := {|
  grp_map := {| morphism := fun a =>
      existT (fun b => GrpImage (sub_mono u) b) (sub_mono u a)
             (existT (fun a' => @equiv _ (is_setoid (grp_setoid G))
                                        (sub_mono u a') (sub_mono u a)) a
                     (@Equivalence_Reflexive _ _
                        (@setoid_equiv _ (is_setoid (grp_setoid G)))
                        (sub_mono u a))) |}
|}.
Next Obligation. intros a a' H; simpl. apply proper_morphism; exact H. Qed.
Next Obligation. apply (grp_map_unit (sub_mono u)). Qed.
Next Obligation. apply (grp_map_mul (sub_mono u)). Qed.

Definition grp_image_iso :
  @Isomorphism Grp (SubgroupGrp (grp_image_subgroup (sub_mono u))) (sub_dom u).
Proof.
  unshelve refine (@Build_Isomorphism Grp _ _ grp_image_fwd grp_image_bwd _ _).
  - intro a; simpl; reflexivity.
  - intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition grp_image_to_from :
  grp_sub_of_subgroup G (grp_image_subgroup (sub_mono u)) ≈ u.
Proof.
  exists grp_image_iso.
  intros [b [a Ha]]; simpl. exact Ha.
Defined.

End GrpToFrom.

Definition Grp_WellPoweredAt_up (G : Grp) : WellPoweredAt G :=
  {| wp_index   := Subgroup G ;
     wp_to      := grp_sub_of_subgroup G ;
     wp_from    := fun u => grp_image_subgroup (sub_mono u) ;
     wp_to_from := grp_image_to_from G |}.
