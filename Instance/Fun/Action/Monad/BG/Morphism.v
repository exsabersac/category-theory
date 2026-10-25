Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Instance.Fun.Action.Monad.BG.

Generalizable All Variables.

(* * * #464's two monads are isomorphic in the category of monads / * * #464 的两个单子在单子范畴中是同构的 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.2 Exercise 3, printed p. 142 (PDF
 p. 151) — maclane:VI.2:ex3; and §VI.2, "Group actions", printed
 p. 141 (PDF p. 150)
 Book: Riehl, "Category Theory in Context", 2nd ed., Exercise 5.5.iv,
 printed p. 208 (PDF p. 228) — riehl:5.5:exiv
 nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
 monads")

 WHAT THIS FILE DOES.  Instance/Fun/Action/Monad/BG.v (#464) has two
 monads on Sets with the same functor data, M × X and M × f: [ActMonad
 M] of Instance/Fun/Action/Monad.v, whose unit is Mac Lane's printed
 η x = (u, x), and [BGMonad M], induced by that file's adjunction, whose
 unit is (u u, x).  Their multiplications agree at every triple
 ([BG_join_ActMonad]).  For want of a record of monad morphisms, BG.v
 related them by three separate facts ([BG_T_ActF], [BG_ret_ActMonad],
 [BG_join_ActMonad]) and built Mac Lane's θ* for this instance by hand
 ([BG_Act_EM]); its header says so ("θ* is built for this instance
 alone, with no general record of monad morphisms").  This file states
 the relation with Monad/Morphism.v and takes θ* from Monad/Morphism/
 Algebra.v.  BG.v is not changed: restated for the general θ*, its
 readback [BG_Act_EM_alg] would be refused (below).

 THE MORPHISMS.  [BG_theta M : MonadHom (ActMonad M) (BGMonad M)] and
 [BG_theta_inv M] the other way, each with the identity of Sets as
 every component ([BG_theta_component], [BG_theta_inv_component], at
 [eq_refl]).  Their unit laws are M's unit law [mon_op_unit_l], one way
 and back; naturality and the multiplication laws hold pointwise by
 reflexivity.  [BG_theta_iso]: the two are inverse in Monad/
 Morphism.v's [Monads Sets], componentwise by reflexivity, so the two
 monads are isomorphic objects of the category of monads, which is the
 one statement BG.v's three facts approximate.

 θ*.  Mac Lane's θ : T ⇝ T' gives θ* : X^{T'} → X^T.  With T =
 [ActMonad M] and T' = [BGMonad M], θ* = mh_EM (BG_theta M) runs from
 the algebras of [BGMonad M] to those of [ActMonad M], the direction of
 [BG_Act_EM].  The two functors agree on carriers, on structure maps as
 functions and on the underlying arrows of algebra maps, at [eq_refl]
 ([BG_theta_EM_carrier], [BG_theta_EM_alg_fun], [BG_theta_EM_hom]), and
 as functors at Cat's ≈ with identity components ([BG_theta_EM]).  They
 are not one functor.  θ* gives an algebra with structure map h the
 structure map h ∘ id, a composite in Sets (Monad/Morphism/Algebra.v's
 [mh_EM_alg]), where [BG_Act_EM] keeps h.  The inverse morphism gives
 [Act_BG_EM], θ* of [BG_theta_inv M], from the algebras of [ActMonad M]
 to those of [BGMonad M]: it assembles into a functor BG.v's
 [Act_BG_alg], which that file "kept as a map on algebras" and "not
 assembled into a functor"; they agree on carriers
 ([Act_BG_EM_carrier]) and on structure maps as functions
 ([Act_BG_EM_alg_fun]).

 STRENGTHS.  By [eq_refl]: the four component and θ* readbacks above,
 [Act_BG_EM_carrier] and [Act_BG_EM_alg_fun].  At ≈: the laws of both
 morphisms, [BG_theta_iso], and [BG_theta_EM].  Refused at [eq_refl],
 by conversion, each pinned in Test/ProbeMonadMorphism468.v with its
 positive controls:
 - the structure map of θ* X as a setoid morphism, against X's own,
 that is BG.v's [BG_Act_EM_alg] restated for θ* (R12; controls C29,
 C31 and C32); and that of [Act_BG_EM] against [Act_BG_alg] (R14;
 control C33);
 - θ* X against [BG_Act_EM] X, as whole objects (R13; controls C28 to
 C30).
 The first two are opacity outside the tree.  The composite h ∘ id in
 Sets is Instance/Sets.v's [setoid_morphism_compose] of
 [setoid_morphism_id], whose properness fields are built by instance
 resolution from the CMorphisms lemmas [Reflexive_partial_app_morphism]
 and [proper_proper_proxy], and [subrelation_id_proper] applied to
 [subrelation_refl], all opaque in the tree and in every copy below.
 In a copy of the probe's dependency closure in which only
 Instance/Sets.v changed, its two fields written as the terms
 fun _ _ H => H and fun a b H => proper_morphism g _ _
 (proper_morphism f a b H) (the change #466 measured for its F1), both
 hold at [eq_refl]; with either field alone written so, both are still
 refused.
 Neither is changed by turning every [Qed] of that closure into
 [Defined] with [Transparent Obligations] set (Instance/Sets.v,
 Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/Grp/Free.v
 keeping their [Qed]s).  The whole-object refusal is not opacity: it
 stands in that transparent copy, in the copy with the two fields
 written as terms, and in a copy with both changes, where the carriers
 and structure maps convert and the unit law [t_id] and the action law
 [t_action] of the two algebras are each refused alone.  θ*'s laws are
 Algebra.v's proof chains through [mh_ret] and [mh_join], BG.v's pass
 the variable algebra's own laws along [mon_op_unit_l]; the two differ
 at neutral terms of the variable carrier setoid (argued from the terms,
 not measured further).
 CORRECTION (#1347): the copy with the two fields written as terms is
 now the tree: the first two refusals, R12 and R14, hold at [eq_refl]
 and are controls of the probe, and their attribution to the standard
 library's opacity was right; the whole-object refusal, R13, still
 stands.

 UNIVERSES, read off [About].  Every constant binds [@{o so}] with o < so,
 M : MonObject@{o o o}, except [BG_theta_iso], which adds the object and
 hom levels m1 and m2 of [Monads@{so o m1 m2} Sets], at or above so, and
 the caps o, so <= Projections.u0/u1 of the sigma objects of [Monads], and
 [BG_theta_EM], which adds c with o < c and so < c, the levels of
 [Cat@{c so so so o}], first carried by Instance/Cat.v's [Cat].  o < so is
 first carried by Instance/Sets.v's [Sets].  The two morphisms have
 exactly the block of [BGMonad] and [ActMonad]: the caps compose and ID
 from [Sets], prod_rect and projections from the product carrier, and
 Logic_lemmas.equality and so <= projections from Theory/Adjunction.v's
 [Build_Adjunction'], all named in BG.v's UNIVERSES paragraph.  The θ*
 readbacks and [Act_BG_EM] have the block of [BG_Act_EM], which adds o <=
 Projections.u1 and so <= Projections.u0 from [EilenbergMoore]'s sigma
 objects.  A [simpl] in the proof of [BG_theta_EM] added the strict bound
 o < Projections.u0, as it did to [BG_Act_EM] (BG.v's header); the proof
 has none, and the bound is gone (measured both ways).  No [Set] and no
 equation occur.

 NOT DELIVERED.  BG.v is not rewired onto θ*: its readback
 [BG_Act_EM_alg] would be refused, as above.  The isomorphism in Cat
 between the two Eilenberg–Moore categories that Monad/Morphism/
 Algebra.v's [Monads_EM] makes of [BG_theta_iso] is not stated; BG.v
 already relates both to Set^BG through its comparison functors.
 CORRECTION (#1347): [BG_Act_EM_alg] restated for θ* is no longer
 refused (R12, above); BG.v is still not rewired. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，Springer GTM 5, 1998年，第VI.2节 练习3，印刷版第142页（PDF第151页）—— maclane:VI.2:ex3；以及第VI.2节，“群作用”，印刷版第141页（PDF第150页）
 书籍：Riehl，《语境中的范畴论》，第2版，练习5.5.iv，印刷版第208页（PDF第228页）—— riehl:5.5:exiv
 nLab：https://ncatlab.org/nlab/show/monad（“单子2-范畴”部分）这个文件的作用。Instance/Fun/Action/Monad/BG.v (#464) 在集合上有两个相同函子数据的单子，M × X 和 M × f: [ActMonad M]，来自 Instance/Fun/Action/Monad.v，其单位是 Mac Lane 打印的 η x = (u, x)，以及 [BGMonad M]，由该文件的伴随引出，其单位是 (u u, x)。它们的乘法在每一个三元组 ([BG_join_ActMonad]) 上都一致。由于缺少单子态射的记录，BG.v 用三个独立的事实 ([BG_T_ActF], [BG_ret_ActMonad], [BG_join_ActMonad]) 来关联它们，并手工构建了此实例的 Mac Lane θ* ([BG_Act_EM])；其头部说明了这一点（“θ* 仅为该实例构建，没有单子态射的通用记录”）。该文件说明了与 Monad/Morphism.v 的关系，并从 Monad/Morphism/Algebra.v 中获取 θ*。BG.v 没有改变：针对一般的 θ* 重新表述，其读回 [BG_Act_EM_alg] 会被拒绝（如下）。

 态射。[BG_theta M : MonadHom (ActMonad M) (BGMonad M)] 和 [BG_theta_inv M] 反向，每个的每个分量都是集合的恒等（[BG_theta_component]、[BG_theta_inv_component]，在 [eq_refl]）。它们的单位律是 M 的单位律 [mon_op_unit_l]，一方向和反方向；自然性和乘法律按点通过自反性成立。[BG_theta_iso]：两者在 Monad/Morphism.v 的 [Monads Sets] 中是逆的，按分量通过自反性，因此这两个 monad 是 monads 范畴中的同构对象，这就是 BG.v 的三个事实所近似表达的唯一陈述。θ*。Mac Lane 的 θ : T ⇝ T' 给出 θ* : X^{T'} → X^T。对于 T = [ActMonad M] 和 T' = [BGMonad M]，θ* = mh_EM (BG_theta M) 从 [BGMonad M] 的代数到 [ActMonad M] 的代数运行，方向为 [BG_Act_EM]。两个函子在承载对象上、作为函数的结构映射上以及代数映射的基本箭头上在 [eq_refl] (ZWZ22WZZ, ZWZ23WZZ, ZWZ24WZZ) 上一致，并且作为函子在 Cat's ≈ 上带有恒等分量 (ZWZ25WZZ) 时也一致。但它们不是同一个函子。θ* 给出了一个具有结构映射 h 的代数，其结构映射为 h ∘ id，是 Sets (Monad/Morphism/Algebra.v 的 [mh_EM_alg]) 中的复合，其中 [BG_Act_EM] 保持 h。逆态射给出
 [Act_BG_EM]，θ* 从 [BG_theta_inv M] 的代数
 到 [ActMonad M] 的代数：它组装成一个函子 BG.v 的
 [Act_BG_alg]，该文件“保持为代数上的映射”，而“未组装成函子”；它们在载体
 （[Act_BG_EM_carrier]）和作为函数的结构映射
 （[Act_BG_EM_alg_fun]）上是一致的。优势。由 [eq_refl] ：上述四个组成部分和 θ* 读回，[Act_BG_EM_carrier] 和 [Act_BG_EM_alg_fun]。在 ≈ 时：两种态射的定律，[BG_theta_iso] 和 [BG_theta_EM]。在 [eq_refl] 被拒绝，通过转换，每个都在 Test/ProbeMonadMorphism468.v 中固定，并配有其正向对照：
 - 将 θ* X 的结构映射作为集合同态，与 X 自身的映射相比，即 BG.v 的 [BG_Act_EM_alg] 对 θ* 重新陈述（R12；对照 C29、C31 和 C32）；以及 [Act_BG_EM] 对 [Act_BG_alg]（R14；对照 C33）；
 - θ* X 与 [BG_Act_EM] X 作为整体对象对照（R13；对照 C28 至 C30）。前两个在树之外是不透明的。在集合（Sets）中复合函数 h ∘ id 是 Instance/Sets.v 中 [setoid_morphism_compose] 的 [setoid_morphism_id]，其中其 properness 字段是通过从 CMorphisms 引理 [Reflexive_partial_app_morphism] 和 [proper_proper_proxy]，以及 [subrelation_id_proper] 应用于 [subrelation_refl] 的实例解析构建的，在树中以及所有下层副本中都是不透明的。在探针的依赖闭包的一个副本中，如果只有 Instance/Sets.v 改变，其两个字段被写成如下项：fun _ _ H => H 和 fun a b H => proper_morphism g _ _ (proper_morphism f a b H)（其 F1 的变化 #466 被测量），都在 [eq_refl] 上成立；即使其中任一字段单独如此书写，仍然被拒绝。通过将该闭包的每个 [Qed] 转换为 [Defined] 并设置 [Transparent Obligations]（Instance/Sets.v、Structure/Cartesian/Closed.v、Instance/Grp.v 和 Instance/Grp/Free.v 保留其 [Qed]）也不会改变任何字段。整体对象的拒绝不是不透明：它存在于那个透明拷贝中，在两个字段作为项写入的拷贝中，以及在两个更改都存在的拷贝中，其中载体和结构映射被转换，两个代数的单位律 [t_id] 和作用律 [t_action] 各自单独被拒绝。θ* 的律是 Algebra.v 通过 [mh_ret] 和 [mh_join] 的证明链，BG.v 通过 [mon_op_unit_l] 传递变量代数自身的律；两者在变量载体集合等价类的中性项上有所不同（从项出发论证，而没有进一步衡量）。更正 (#1347)：包含两个字段作为术语的副本现在是树状结构：前两个拒绝，R12 和 R14，在 [eq_refl] 上有效，并且是探针的控制，它们归因于标准库的不透明性是正确的；整体对象拒绝，R13，仍然有效。UNIVERSES，读作 [About]。每个常数将 [@{o so}] 与 o < so 绑定，M : MonObject@{o o o}，除了 [BG_theta_iso]，它添加了 [Monads@{so o m1 m2} Sets] 的对象和同态层 m1 和 m2，位于 so 或更高，以及 [Monads] 的 sigma 对象的上限 o，so <= Projections.u0/u1，以及 [BG_theta_EM]，它添加了 c，满足 o < c 和 so < c，ZW68WZZ 的层级，首先由 Instance/Cat.v 的 [Cat] 承载。o < so 首次由 Instance/Sets.v 的 [Sets] 承载。这两个态射恰好拥有 [BGMonad] 和 [ActMonad] 的块：上限可以组合并来自 [Sets] 的 ID，prod_rect 和投影来自积载体，以及 Logic_lemmas.equality 和 so <= projections 来自 Theory/Adjunction.v 的 [Build_Adjunction']，所有内容都在 BG.v 的 UNIVERSES 段中命名。θ* 的回读和 [Act_BG_EM] 拥有 [BG_Act_EM] 的块，它从 [EilenbergMoore] 的 sigma 对象添加了 o <= Projections.u1 和 so <= Projections.u0。在 [BG_theta_EM] 的证明中，[simpl] 添加了严格界 o < Projections.u0，就像对 [BG_Act_EM]（BG.v 的头部）所做的那样；该证明没有，界限也消失了（两种方式测量）。没有 [Set]，也没有方程出现。

 未交付。BG.v 未重新连接到 θ*：其回读 [BG_Act_EM_alg] 会被拒绝，如上所述。Cat 中两个 Eilenberg–Moore 范畴之间的同构，通过 Monad/Morphism/Algebra.v 的 [Monads_EM] 对 [BG_theta_iso] 的构造，并未说明；BG.v 已通过其比较函子将两者都关联到 Set^BG。
 更正（#1347）：为 θ* 重新声明的 [BG_Act_EM_alg] 不再被拒绝（见上 R12）；BG.v 仍未重新连接。
*)

(* * ** θ : ActMonad M ⟶ BGMonad M, identity components / * ** θ : ActMonad M ⟶ BGMonad M，恒等分量 *)

Definition BG_theta@{o so | o < so +} (M : MonObject@{o o o}) :
  MonadHom@{so o} (ActMonad@{o so} M) (BGMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (ActF@{o so} M) (U_BG@{o so} M ◯ F_BG@{o so} M)
       (ActMonad@{o so} M) (BGMonad@{o so} M)
       (Build_Transform'@{so o o so o o}
          (F:=ActF@{o so} M) (G:=U_BG@{o so} M ◯ F_BG@{o so} M)
          (fun X => @id Sets@{o so} (act_prod M X)) _) _ _).
  - intros X Y f p. simpl. split; reflexivity.
  - intros X x. simpl.
    split; [ symmetry; exact (mon_op_unit_l mon_unit) | reflexivity ].
  - intros X p. simpl. split; reflexivity.
Defined.

Example BG_theta_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(* * ** θ⁻¹ : BGMonad M ⟶ ActMonad M, identity components / * ** θ⁻¹ : BGMonad M ⟶ ActMonad M，恒等分量 *)

Definition BG_theta_inv@{o so | o < so +} (M : MonObject@{o o o}) :
  MonadHom@{so o} (BGMonad@{o so} M) (ActMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M) (ActF@{o so} M)
       (BGMonad@{o so} M) (ActMonad@{o so} M)
       (Build_Transform'@{so o o so o o}
          (F:=U_BG@{o so} M ◯ F_BG@{o so} M) (G:=ActF@{o so} M)
          (fun X => @id Sets@{o so} (act_prod M X)) _) _ _).
  - intros X Y f p. simpl. split; reflexivity.
  - intros X x. simpl. split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
  - intros X p. simpl. split; reflexivity.
Defined.

Example BG_theta_inv_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta_inv@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(* The two are inverse in [Monads Sets]. / 这两者在 [Monads Sets] 中是相反的。 *)

Definition BG_theta_iso@{o so m1 m2 |
  o < so, o <= m1, o <= m2, so <= m1, so <= m2 +} (M : MonObject@{o o o}) :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (ActF@{o so} M; ActMonad@{o so} M)
    (U_BG@{o so} M ◯ F_BG@{o so} M; BGMonad@{o so} M).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (ActF@{o so} M; ActMonad@{o so} M)
    (U_BG@{o so} M ◯ F_BG@{o so} M; BGMonad@{o so} M)
    (BG_theta@{o so} M) (BG_theta_inv@{o so} M) _ _).
  - intros X p. simpl. split; reflexivity.
  - intros X p. simpl. split; reflexivity.
Defined.

(** ** θ* against #464's [BG_Act_EM] / ** θ* 对抗 #464 的 [BG_Act_EM] *)

Example BG_theta_EM_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)
    = `1 (fobj[BG_Act_EM@{o so} M] x) := eq_refl.

Example BG_theta_EM_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _
              (`2 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)) p)
    = (fun p => @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) p)
  := eq_refl.

Example BG_theta_EM_hom@{o so | o < so +} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  t_alg_hom[fmap[mh_EM@{so o so so} (BG_theta@{o so} M)] f]
    = t_alg_hom[fmap[BG_Act_EM@{o so} M] f] := eq_refl.

Definition BG_theta_EM@{o so c | o < so, o < c, so < c +}
  (M : MonObject@{o o o}) :
  @equiv _
    (@homset Cat@{c so so so o}
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M)))
    (mh_EM@{so o so so} (BG_theta@{o so} M)) (BG_Act_EM@{o so} M).
Proof.
  unshelve eexists.
  - intros x.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. reflexivity.
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. reflexivity.
    + intros z. reflexivity.
    + intros z. reflexivity.
  - intros x y f z. reflexivity.
Defined.

(* * ** θ⁻¹* assembles #464's [Act_BG_alg] into a functor / * ** θ⁻¹* 将 #464 的 [Act_BG_alg] 组装成一个函子 *)

Definition Act_BG_EM@{o so | o < so +} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so}
      (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M) :=
  mh_EM@{so o so so} (BG_theta_inv@{o so} M).

Example Act_BG_EM_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  `1 (fobj[Act_BG_EM@{o so} M] x) = `1 x := eq_refl.

Example Act_BG_EM_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _ (`2 (fobj[Act_BG_EM@{o so} M] x)) p)
    = (fun p => @t_alg _ _ _ _ (Act_BG_alg@{o so} M (`1 x) (`2 x)) p)
  := eq_refl.
