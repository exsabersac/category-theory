Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Universal.Arrow.Dual.

Generalizable All Variables.

(**
* Determination of an adjunction by its counit and by couniversal
      arrows

    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, §IV.1 Theorem 2 -- maclane:IV.1:thm2.
    Book: Awodey, "Category Theory", 2nd ed., §9.2 Corollary 9.5,
          printed pp. 222-223 -- awodey:9.2:cor5.

    WHAT WAS ALREADY THERE, AND THE ISSUE'S OWN ACCOUNT OF IT IS STALE.
    #347's "Current state" says a whole-tree search for couniversal
    arrows "returns nothing" and that Theory/Universal/Arrow.v "has no
    dual".  Both are false: Theory/Universal/Arrow/Dual.v supplies
    [CouniversalArrow], [coarrow],
    [ump_couniversal_arrows],
    [RightAdjointFunctorFromCouniversalArrows] and
    [AdjunctionFromCouniversalArrows].  Every one of those is
    CONSUMED here and none re-derived, which is what that issue's own QA
    correction directs.

    THE DISTINCTION THAT DEFINES THIS FILE IS A DIRECTION, AND IT IS EASY
    TO MISS.  Dual.v already carries a lemma named
    [counit_couniversal].  It takes a couniversal family as DATA and
    describes the adjunction that file BUILDS -- every adjunction named
    there is [AdjunctionFromCouniversalArrows] of that family -- so it
    never starts from an arbitrary adjunction.  What was open, and is
    delivered here, is the CONVERSE: from an ARBITRARY [F ⊣ U],
    [adj_counit_couniversal] exhibits each counit component as a
    [CouniversalArrow] PACKAGED AS THE CLASS, which is the bar the issue
    sets ("not merely that the equational form [adj_univ_impl] holds").
    Neither Theory/Universal/Arrow.v nor its dual contains any passage
    from an adjunction to a (co)universal arrow.

    STRENGTHS, MEASURED STRICT-FIRST -- AND ONLY ONE OF THEM
    DISCRIMINATES.  The arrow readback [coarrow (adj_counit_couniversal
    c) = counit] is [eq_refl], where the donor's [counit_couniversal]
    reaches only [≈]; building the couniversal arrow FROM the counit
    makes the counit definitionally its arrow, whereas recovering the
    counit from a given family leaves an [fmap[F] id] residue.  **The
    OBJECT readback is NOT evidence of that**: it is [eq_refl] on both
    sides (Dual.v's [right_adjoint_obj] is [reflexivity]) and also on
    this file's own other direction ([couniversal_of_counit_obj]), so it
    is parity, not superiority.  Only the arrow half separates them.

    The [eq_refl] object readbacks are nonetheless load-bearing rather
    than decorative: [couniversal_of_counit_med] and
    [adjunction_of_counit_unit] only TYPECHECK because the object
    readback is definitional.

    THE ONE [≈]-ONLY STEP IS THE MEDIATOR, and the honest statement of
    its cause is narrower than "donor opacity" alone.  What the contrast
    below establishes is that the failure is not a property of the
    couniversal arrow in general: [coarrow] and [coarrow_obj] of the SAME
    arrow do reduce.  That does NOT by itself isolate the [Qed] on
    [ump_universal_arrows] (Theory/Universal/Arrow.v), since those
    two never route through [ump_*] at all and so would reduce under any
    competing hypothesis.  An isolating experiment -- the same statement
    against a transparent clone of that donor -- was run during review
    and DOES confirm the attribution, and it further shows the [≈] could
    be strengthened by making the donor transparent; that experiment is
    NOT shipped here, and changing Theory/Universal/Arrow.v is out of
    scope for this issue.

    WHAT THE UNIT SIDE DOES AND DOES NOT DELIVER.  [UnitPresentation]
    gives Mac Lane's FIRST presentation its own record -- a left adjoint,
    a right adjoint, and a unit whose every component is universal --
    with passages BOTH ways ([unit_presentation_of_adjunction],
    [adjunction_of_unit_presentation]).  That is a DICTIONARY, not a
    separation in this tree's usual sense: nothing here proves the two
    presentations differ.  And unlike the counit side, **no round trip is
    proved**: there is no statement that
    [adjunction_of_unit_presentation (unit_presentation_of_adjunction A)]
    agrees with [A], nor any relating the recovered [up_unit] to
    [unit A].  [unit_presentation_transpose] and its untransposed sibling
    are [eq_refl] BY CONSTRUCTION -- [adjunction_of_unit_presentation]
    defines its transposes as exactly those terms -- so they pin a
    definition rather than recovering anything, and neither passes
    through [unit_presentation_of_adjunction].

    NOT DELIVERED: the unit-side round trip just described; no dual of
    the [UnitPresentation] packaging (a counit presentation as its own
    record); no naturality of the couniversal family in [c]; no
    comparison with Theory/Universal/Element.v's universal-element
    route; and no change to the transparency of
    [ump_universal_arrows]. 

--------
* 通过其单位和普遍性来确定附加物
 箭头

nLab：https://ncatlab.org/nlab/show/adjoint+functor
 nLab：https://ncatlab.org/nlab/show/universal+morphism
 维基百科：https://en.wikipedia.org/wiki/Adjoint_functors

书：Mac Lane，“工作数学家的类别”，第二版，
 GTM 5，Springer 1998，第 IV.1 定理 2 -- Maclane:IV.1:thm2。 
书籍：Awodey，“范畴论”，第二版，§9.2 推论 9.5，
 印刷第 222-223 页 -- awodey:9.2:cor5。

那里已经有什么了，而本期自己对它的描述也已经过时了。 
#347 的“当前状态”表示对 couniversal 进行全树搜索
 arrows“不返回任何内容”并且 Theory/Universal/Arrow.v“没有
 双”。 两者都是错误的：Theory/Universal/Arrow/Dual.v 供应
 [CouniversalArrow]、[coarrow]、
 [ump_couniversal_arrows]，
 [RightAdjointFunctorFromCouniversalArrows] 和
 [AdjunctionFromCouniversalArrows]。 其中每一项都是
 此处已消耗，没有重新派生，这就是该问题自己的 QA
 修正指示。

定义此文件的区别是一个方向，而且很简单
 错过。 Dual.v 已经带有一个名为
 [counit_couniversal]。 它以一个通用族作为 DATA 并
 描述文件构建的附加项——每个名为
 该系列有 [AdjunctionFromCouniversalArrows]——所以它
 绝不会从任意附加词开始。 什么是开放的，什么是
 这里交付的是匡威：来自任意 [F ⊣ U]，
 [adj_counit_couniversal] 将每个单元组件展示为
 [CouniversalArrow] 封装为类，这是问题所在
 集（“不仅仅是等式形式 [adj_univ_impl] 成立”）。 
Theory/Universal/Arrow.v 及其对偶均不包含任何段落
 从附加到（共同）通用箭头。

严格优先衡量的优势——而且只有其中之一
 歧视。 箭头回读 [coarrow (adj_counit_couniversal
 c) = counit] 是 [eq_refl]，其中捐赠者的 [counit_couniversal]
 仅达到 [≈]； 从国家建立通用箭头
 使计数定义为箭头，而恢复
 来自给定家族的计数留下 [fmap[F] id] 残基。 **该
 对象回读并不是这一点的证据**：两者都是 [eq_refl]
 侧面（Dual.v 的 [right_adjoint_obj] 是 [reflexivity]）以及
 该文件自己的另一个方向（[couniversal_of_counit_obj]），所以它
 是平等，而不是优越。 只有箭头的一半将它们分开。

[eq_refl] 对象读回仍然是承重的
 比装饰性：[couniversal_of_counit_med] 和
 [adjunction_of_counit_unit] 仅 TYPECHECK 因为对象
 回读是定义性的。

[≈] 唯一的一步是调解者，以及诚实的声明
 其原因比单纯的“捐助者不透明”要窄。 有什么对比
 下面确定的是，故障不是
 一般通用箭头：[coarrow] 和 [coarrow_obj] 相同
 箭头确实减少了。 这本身并不隔离 [Qed]
 [ump_universal_arrows] (Theory/Universal/Arrow.v)，因为那些
 两个根本不会通过 [ump_*] 路由，因此在任何情况下都会减少
 竞争假设。 一个孤立的实验——同样的说法
 针对该捐赠者的透明克隆——在审查期间运行
 并且确实确认了归属，这进一步表明 [≈] 可以
 通过使捐助者透明化来加强； 那个实验是
 此处未发货，并且更改 Theory/Universal/Arrow.v 已过时
 这个问题的范围。

单位方提供和不提供的内容。 保护29X
 为 Mac Lane 的 FIRST 演示提供了自己的记录——左伴随，
 一个右伴随，一个其每个分量都是通用的单位——
 双向通道（[unit_presentation_of_adjunction]，
 [adjunction_of_unit_presentation]）。 那是一本字典，而不是一本
 这棵树通常意义上的分离：这里没有任何东西可以证明两者
 演示文稿有所不同。 与国家一侧不同，**没有往返
 证明**：没有任何声明表明
 保护32X
 同意 [A]，也不同意将恢复的 [up_unit] 与
 [unit A]。 [unit_presentation_transpose] 及其未转置的兄弟姐妹
 是 [eq_refl] 的构造 -- [adjunction_of_unit_presentation]
 将其转置定义为这些术语 - 所以它们固定一个
 定义而不是恢复任何东西，并且都没有通过
 通过 [unit_presentation_of_adjunction]。

未交付：刚刚描述的单元端往返； 没有双重的
 [UnitPresentation] 包装（作为其自己的联合展示
 记录）； [c] 中没有普遍族的自然性； 不
 与 Theory/Universal/Element.v 的 universal-element 的比较
 路线； 并且透明度没有改变
 [ump_universal_arrows]。 
*)


Section CounitCouniversal.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

#[local] Existing Instance A.

(*
Mac Lane §IV.1 Theorem 2, the converse leg: each counit component is a
   couniversal arrow, PACKAGED as one. 

--------
Mac Lane §IV.1 定理 2，逆命题：每个单位分量是一个
 通用箭头，包装为一体。 
*)
Definition adj_counit_couniversal (c : C) : CouniversalArrow c F.
Proof using A U.
  unshelve eapply (couniversal_arrow_from_UMP c F (U c) counit).
  intros d' f.
  unshelve eexists ((to adj[A] f)).
  - exact (snd (adj_univ_impl f (to adj[A] f)) (reflexivity _)).
  - intros v Hv.
    exact (fst (adj_univ_impl f v) Hv).
Defined.

Example adj_counit_couniversal_obj (c : C) :
  coarrow_obj (adj_counit_couniversal c) = U c := eq_refl.

Example adj_counit_couniversal_arrow (c : C) :
  coarrow (adj_counit_couniversal c) = @counit C D F U A c := eq_refl.

(*
The mediator of that couniversal arrow is the forward transpose -- up to
   `≈` only, and the cause is DONOR OPACITY that DISCRIMINATES: [coarrow] and
   [coarrow_obj] above reduce because they are transparent projections of the
   transparent [couniversal_arrow_from_UMP], whereas the mediator is read out
   of [ump_couniversal_arrows], whose primal donor [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is closed with [Qed]. 

--------
该通用箭头的中介是前向转置——直到
 仅限`≈`，原因是捐助者不透明性歧视：[coarrow] 和
 [coarrow_obj] 上面减少了，因为它们是透明投影
 透明[couniversal_arrow_from_UMP]，而中介者被读出
 [ump_couniversal_arrows] 的原始供体 [ump_universal_arrows]
 (Theory/Universal/Arrow.v) 用 [Qed] 关闭。 
*)
Lemma adj_counit_couniversal_med (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal c) f)
    ≈ to adj[A] f.
Proof using A U.
  symmetry.
  exact (fst (adj_univ_impl f _)
             (unique_property
                (ump_couniversal_arrows (adj_counit_couniversal c) f))).
Qed.

Lemma adj_counit_factor_unique {x y : C} (f : x ~{C}~> y)
      (g : U x ~{D}~> U y) :
  f ∘ @counit C D F U A x ≈ @counit C D F U A y ∘ fmap[F] g →
  g ≈ fmap[U] f.
Proof using A U.
  intro Hg.
  rewrite <- (fst (adj_univ_impl (f ∘ counit) g) Hg).
  symmetry.
  apply fmap_to_adj_counit.
Qed.

End CounitCouniversal.

Section CounitRoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition counit_couniversal_family : ∀ c : C, CouniversalArrow c F :=
  adj_counit_couniversal A.

Definition right_adjoint_of_counit : C ⟶ D :=
  RightAdjointFunctorFromCouniversalArrows F counit_couniversal_family.

Definition adjunction_of_counit : F ⊣ right_adjoint_of_counit :=
  AdjunctionFromCouniversalArrows F counit_couniversal_family.

Example right_adjoint_of_counit_obj (c : C) :
  fobj[right_adjoint_of_counit] c = fobj[U] c := eq_refl.

Lemma adjunction_of_counit_counit (c : C) :
  @counit C D F right_adjoint_of_counit adjunction_of_counit c
    ≈ @counit C D F U A c.
Proof using A U.
  exact (counit_couniversal F counit_couniversal_family c).
Qed.

Lemma right_adjoint_of_counit_fmap {x y : C} (f : x ~{C}~> y) :
  fmap[right_adjoint_of_counit] f ≈ fmap[U] f.
Proof using A U.
  apply (adj_counit_factor_unique A).
  rewrite <- (adjunction_of_counit_counit x).
  rewrite <- (adjunction_of_counit_counit y).
  symmetry.
  exact (adj_counit_naturality adjunction_of_counit f).
Qed.

Lemma right_adjoint_of_counit_iso : right_adjoint_of_counit ≈ U.
Proof using A U.
  exists (fun c => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  apply right_adjoint_of_counit_fmap.
Qed.

Lemma adjunction_of_counit_to {x : D} {y : C} (g : F x ~{C}~> y) :
  to adj[adjunction_of_counit] g ≈ to adj[A] g.
Proof using A U.
  symmetry.
  apply (fst (@adj_univ_impl C D F U A x y g _)).
  rewrite <- (adjunction_of_counit_counit y).
  exact (snd (@adj_univ_impl C D F right_adjoint_of_counit
                adjunction_of_counit x y g _) (reflexivity _)).
Qed.

Lemma adjunction_of_counit_from {x : D} {y : C} (h : x ~{D}~> U y) :
  from adj[adjunction_of_counit] h ≈ from adj[A] h.
Proof using A U.
  rewrite (@from_adj_counit C D F right_adjoint_of_counit
             adjunction_of_counit x y h).
  rewrite (@from_adj_counit C D F U A x y h).
  now rewrite (adjunction_of_counit_counit y).
Qed.

Lemma adjunction_of_counit_unit (d : D) :
  @unit C D F right_adjoint_of_counit adjunction_of_counit d
    ≈ @unit C D F U A d.
Proof using A U. exact (adjunction_of_counit_to id). Qed.

End CounitRoundTrip.

(** ** The other composite: couniversal arrows, adjunction, counit  / ** 其他复合词：通用箭头、附加词、复合词*)

Section CouniversalRoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context (H : ∀ c : C, CouniversalArrow c F).

Example couniversal_of_counit_obj (c : C) :
  coarrow_obj (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
    = coarrow_obj (H c) := eq_refl.

Lemma couniversal_of_counit_arrow (c : C) :
  coarrow (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
    ≈ coarrow (H c).
Proof using H. exact (counit_couniversal F H c). Qed.

Lemma couniversal_of_counit_med (c : C) :
  cua_med (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
          (H c) ≈ id.
Proof using H.
  apply cua_med_unique.
  rewrite fmap_id, id_right.
  symmetry.
  apply couniversal_of_counit_arrow.
Qed.

Lemma couniversal_of_counit_iso (c : C) :
  couniversal_arrow_iso
    (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c) (H c)
    ≈ iso_id.
Proof using H.
  apply to_equiv_implies_iso_equiv; simpl.
  apply couniversal_of_counit_med.
Qed.

End CouniversalRoundTrip.

(**
** Mac Lane's first presentation: a natural unit whose every component
       is universal 

--------
** Mac Lane 的首次展示：一个自然单元，其每个组件
 是普遍的 
*)

Section UnitSide.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class UnitPresentation := {
  up_unit : Id[D] ⟹ U ◯ F;
  up_universal {d : D} {c : C} (f : d ~{D}~> U c) :
    ∃! g : F d ~{C}~> c, f ≈ fmap[U] g ∘ transform[up_unit] d
}.

Definition unit_presentation_of_adjunction (A : F ⊣ U) : UnitPresentation.
Proof.
  unshelve eapply Build_UnitPresentation.
  - unshelve eapply Build_Transform.
    + exact (fun d => @unit C D F U A d).
    + exact (fun x y f => adj_unit_naturality A f).
    + exact (fun x y f => symmetry (adj_unit_naturality A f)).
  - intros d c f; simpl.
    unshelve eexists (from adj[A] f).
    + rewrite <- (@to_adj_unit C D F U A d c (from adj[A] f)).
      symmetry.
      exact (@from_adj_comp_law C D F U A d c f).
    + intros v Hv.
      symmetry.
      apply (snd (@adj_univ C D F U A d c v f)).
      rewrite (@to_adj_unit C D F U A d c v).
      now symmetry.
Defined.

Definition adjunction_of_unit_presentation (P : UnitPresentation) : F ⊣ U.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros d c.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun g => fmap[U] g ∘ transform[up_unit] d).
      * abstract (intros g1 g2 Hg; apply compose_respects;
                  [ exact (fmap_respects _ _ g1 g2 Hg) | reflexivity ]).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun f => unique_obj (up_universal f)).
      * abstract (intros f1 f2 Hf; apply uniqueness;
                  etransitivity; [ exact Hf
                                 | exact (unique_property (up_universal f2)) ]).
    + abstract (intro f; symmetry; exact (unique_property (up_universal f))).
    + abstract (intro g; apply uniqueness; reflexivity).
  - abstract (intros x y z f g; simpl;
              rewrite fmap_comp, <- comp_assoc;
              rewrite (@naturality _ _ _ _ up_unit _ _ g);
              now rewrite comp_assoc).
  - abstract (intros x y z f g; simpl;
              now rewrite fmap_comp, <- comp_assoc).
Defined.

(* Mac Lane's transpose formula, on the nose.  / 麦克莱恩的转置公式，在鼻子上。*)
Example unit_presentation_transpose (P : UnitPresentation)
        {d : D} {c : C} (g : F d ~{C}~> c) :
  to adj[adjunction_of_unit_presentation P] g
    = fmap[U] g ∘ transform[up_unit] d := eq_refl.

Example unit_presentation_untranspose (P : UnitPresentation)
        {d : D} {c : C} (f : d ~{D}~> U c) :
  from adj[adjunction_of_unit_presentation P] f
    = unique_obj (up_universal f) := eq_refl.

End UnitSide.
