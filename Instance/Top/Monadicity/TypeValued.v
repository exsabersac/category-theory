Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(* * * The underlying-set functor of the Type-valued [Top] is not monadic / * * 类型值 [Top] 的底层集合函子不是幺半的 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §VI.3, book p. 144 (PDF p. 153), read from the page image: for the
 forgetful functor G : Top → Set and its left adjoint D, the discrete
 space, the comparison functor "is not an isomorphism, and not even
 an equivalence" (catalog id maclane:VI.3:remark1).
 nLab: https://ncatlab.org/nlab/show/monadic+functor

 WHAT THIS FILE IS.  Instance/Top/Monadicity.v states Mac Lane's remark
 over Instance/Top/Prop.v's Prop-valued [PTopCat], where the discrete
 space is a left adjoint as an [Adjunction] record.  This file states
 what of it is formable over the tree's own Type-valued [Top]
 (Instance/Top.v): that its underlying-set functor is not monadic,
 [Top_Forget_not_Monadic].

 WHAT IS NOT FORMABLE, AND WHY THE NEGATION IS.  [Top_Forget] goes from
 [Top@{h o}], whose homs sit at [h] above the points at [o], to the
 lifted [Sets@{h so}], while [Top_Discrete] comes from the unlifted
 [Sets@{o so}]; an [Adjunction] record asks both functors to share one
 [Sets], so [Top_Discrete ⊣ Top_Forget] is unformable at every universe
 assignment (Instance/Top/Forgetful.v's header;
 Test/ProbeUniversalArrows312.v pins the refusal).  With it go the
 induced monad and the comparison functor.  [Monadic Top_Forget]
 (Monad/Comparison.v) is formable all the same: [Top@{h o}] and
 [Sets@{h so}] share the hom level [h], and [Monadic] quantifies over
 left adjoints out of [Sets@{h so}], not over [Top_Discrete].  So its
 negation is a statement here.

 THE PROOF is Instance/Top/Monadicity.v's, by conservativity.  An
 equivalence K is full (Theory/Equivalence/FullFaithful.v's
 [Equivalence_Full]) and the forgetful functor of any Eilenberg-Moore
 category reflects isomorphisms (Monad/Monadicity/BeckObjects.v's
 [em_forget_reflects_isos]).  The identity of [bool] from Instance/
 Top.v's [Bool_Discrete] to its [TwoPoint_Indiscrete] is continuous
 ([top_bool_to_indisc]); its image under K is an algebra map whose
 underlying function is an isomorphism of [Sets], so it has an inverse
 algebra map, and fullness brings that inverse back to a continuous map
 from [TwoPoint_Indiscrete] to [Bool_Discrete] that is the identity on
 points.  [no_top_indisc_to_bool] refutes one: it would make the
 identity continuous, which Instance/Top.v's
 [indiscrete_to_discrete_id_not_continuous] refutes.

 STRENGTH, AND WHAT IT DOES NOT SAY.  [Top_Forget_not_Monadic] holds
 for every left adjoint and every adjunction.  No left adjoint of
 [Top_Forget] is in the tree, and whether one exists at these
 universes is not settled here, so over [Top] the statement may hold
 for want of an adjunction; it is the [PTopCat] form,
 Instance/Top/Monadicity.v's [PForget_not_Monadic], whose adjunction
 part is inhabited ([PDisc_PForget]).  All three constants close with
 [Qed] or are plain terms; the file has no readback.

 UNIVERSES, read off [About] on Rocq 9.1.1; stdlib caps (compose, ID,
 projections, Projections, Logic_lemmas.equality, eq_ind_r, eq_rect_r
 and prod_rect; the first carrier of eq_ind_r is Instance/Top.v's
 [indiscrete_to_discrete_id_not_continuous], that of eq_rect_r the
 [rewrite] in [no_top_indisc_to_bool]) left out.
 [top_bool_to_indisc@{o h}] and [no_top_indisc_to_bool@{o h}]: o < h,
 [Top@{h o}]'s own.  [Top_Forget_not_Monadic@{o h so m m0 m1 m3 m6}]
 states [Monadic@{m m0 m1 h m3 h so m6}], whose block it carries in
 full (h < m0, h and so below m, h below m1 and m3, so below m3, m1
 and m3 below m), with o < h and h < so from [Top_Forget@{o h so}].
 No [Set] and no equation occur.

 NOT DELIVERED.  The induced monad and the comparison functor over
 [Top] (unformable, above); any left adjoint of [Top_Forget], or a
 proof that there is none. 

 --------
 Mac Lane，《为工作中的数学家而设的范畴》，第二版（GTM 5），第 VI.3 节，书本第 144 页（PDF 第 153 页），从页面图像读取：对于忘记函子 G : Top → Set 及其左伴随函子 D（离散空间），比较函子“不是同构，甚至不是等价”（目录编号 maclane:VI.3:remark1）。
 nLab: https://ncatlab.org/nlab/show/monadic+functor

 这个文件是什么。Instance/Top/Monadicity.v 在 Instance/Top/Prop.v 的命题值 [PTopCat] 上陈述了 Mac Lane 的备注，其中离散空间作为 [Adjunction] 记录的左伴随。这个文件陈述了在树自身的类型值 [Top] 上可形成的部分（Instance/Top.v）：其底层集合函子不是单子性的，[Top_Forget_not_Monadic]。什么是不可形成的，以及为什么否定是可行的。[Top_Forget] 从 [Top@{h o}] 出发，其 Hom 位于 [h]，在 [o] 处的点之上，移动到提升的 [Sets@{h so}]，而 [Top_Discrete] 来自未提升的 [Sets@{o so}]；一个 [Adjunction] 记录要求两个函子共享一个 [Sets]，因此 [Top_Discrete ⊣ Top_Forget] 在每个宇宙分配下都是不可形成的（Instance/Top/Forgetful.v 的头文件；Test/ProbeUniversalArrows312.v 证实了拒绝）。随之而来的是诱导出的单子和比较函子。[Monadic Top_Forget]（Monad/Comparison.v）仍然是可形成的：[Top@{h o}] 和 [Sets@{h so}] 共享 Hom 级别 [h]，而 [Monadic] 量化的是 [Sets@{h so}] 的左伴随，而不是 [Top_Discrete]。因此，它的否定在这里是一种陈述。证明是 Instance/Top/Monadicity.v 的，通过守恒性。一个 等价 K 是满的（Theory/Equivalence/FullFaithful.v 的 [Equivalence_Full]），并且任何 Eilenberg-Moore 范畴的遗忘函子会反映同构（Monad/Monadicity/BeckObjects.v 的 [em_forget_reflects_isos]）。从 Instance/Top.v 的 [Bool_Discrete] 到其 [TwoPoint_Indiscrete] 的 [bool] 的恒等映射是连续的（[top_bool_to_indisc]）；其在 K 下的像是一个代数映射，其底层函数是 [Sets] 的同构，因此它有一个逆代数映射，满性将该逆映射带回到一个从 [TwoPoint_Indiscrete] 到 [Bool_Discrete] 的连续映射，它在点上是恒等的。[no_top_indisc_to_bool] 否定了其中之一：它会使恒等映射连续，而 Instance/Top.v 的 [indiscrete_to_discrete_id_not_continuous] 否定了这一点。强度，以及它没有说明的内容。[Top_Forget_not_Monadic] 对每一个左伴随和每一个伴随都成立。[Top_Forget] 的任何左伴随都不在树中，并且在这些宇宙中是否存在尚未确定，因此在 [Top] 上该声明可能因缺少伴随而成立；它是 [PTopCat] 形式，Instance/Top/Monadicity.v 的 [PForget_not_Monadic]，其伴随部分是存在的（[PDisc_PForget]）。所有三个常量都以 [Qed] 关闭或是普通项；该文件没有回读。宇宙，在 Rocq 9.1.1 上读取 [About]；标准库大写（compose, ID, projections, Projections, Logic_lemmas.equality, eq_ind_r, eq_rect_r 和 prod_rect；eq_ind_r 的第一个载体是 Instance/Top.v 的 [indiscrete_to_discrete_id_not_continuous]，eq_rect_r 的载体是 [rewrite] 在 [no_top_indisc_to_bool] 中）被省略。 [top_bool_to_indisc@{o h}] 和 [no_top_indisc_to_bool@{o h}]：o < h，[Top@{h o}] 自己的。[Top_Forget_not_Monadic@{o h so m m0 m1 m3 m6}] 陈述了 [Monadic@{m m0 m1 h m3 h so m6}]，其块完整携带（h < m0，h 且如下 m，h < m1 和 m3，如下 m3，m1 和 m3 < m），以及 o < h 和由 [Top_Forget@{o h so}] 得到的 h < so。未出现 [Set] 和方程。未交付。在 [Top] 上诱导的 monad 和比较函子（不可形成，如上）；[Top_Forget] 的任何左伴随，或证明其不存在的证明。
*)

(*
 The identity of [bool], continuous from the discrete space to the
 indiscrete one (Instance/Top.v's [into_indiscrete_continuous]). 

 --------
 [bool] 的恒等映射，从离散空间连续到无离散空间（Instance/Top.v 的 [into_indiscrete_continuous]）。
*)
Definition top_bool_to_indisc@{o h | o < h +} :
  Bool_Discrete@{o} ~{Top@{h o}}~> TwoPoint_Indiscrete@{o} :=
  @Build_ContinuousMorphism Bool_Discrete@{o} TwoPoint_Indiscrete@{o}
    setoid_morphism_id
    (into_indiscrete_continuous Bool_Discrete@{o} bool_setoid_object@{o o}
       setoid_morphism_id).

(*
 No continuous map back is the identity on points: it would make the
 identity continuous, which Instance/Top.v's
 [indiscrete_to_discrete_id_not_continuous] refutes. 

 --------
 没有连续映射回原点是对点的恒等映射：它会使恒等映射连续，而 Instance/Top.v 的 [indiscrete_to_discrete_id_not_continuous] 反驳了这一点。
*)
Lemma no_top_indisc_to_bool@{o h | o < h +}
  (g : TwoPoint_Indiscrete@{o} ~{Top@{h o}}~> Bool_Discrete@{o}) :
  (∀ b : bool, continuous_map g b = b) → False.
Proof.
  intros Hg.
  apply (@indiscrete_to_discrete_id_not_continuous@{h o}).
  intros U HU.
  apply (open_respects TwoPoint_Indiscrete@{o}
           (fun x => U (continuous_map g x))).
  - intro x; simpl. rewrite (Hg x). split; intro u; exact u.
  - exact (continuity g U HU).
Qed.

Lemma Top_Forget_not_Monadic@{o h so m m0 m1 m3 m6 |
  o < h, h < so, h < m0, so <= m, h <= m1, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 h m3 h so m6} Top_Forget@{o h so} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{h so} _ _
                   (fmap[EM_Forget _] (fmap[K] top_bool_to_indisc@{o h})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_top_indisc_to_bool
           (@prefmap _ _ _ HF TwoPoint_Indiscrete@{o} Bool_Discrete@{o} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF TwoPoint_Indiscrete@{o} Bool_Discrete@{o} g b).
  - exact (Hr b).
Qed.
