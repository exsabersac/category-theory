Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Bicartesian.Matrix.

Generalizable All Variables.

(** * The injections of a coproduct meet in the zero subobject / * 余积的注入在零子对象处相遇 *)

(*
nLab:      https://ncatlab.org/nlab/show/disjoint+coproduct
   nLab:      https://ncatlab.org/nlab/show/zero+object
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Free_product

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7 Exercise 1 (book p. 128, PDF p. 137) asks, of the free product of
   two groups, that its two injections be monic and that their images
   meet in the trivial subgroup, and it names a method.  The in-repo
   catalog's statement summary of the exercise
   (doc/plan/books/maclane/inventory/V.json, entry maclane:V.7:ex1, book
   page 128) reads, on this half: "Using the product G x H, show also
   that the two coproduct injections G -> G + H and H -> G + H are monic,
   and that their images intersect in the identity subgroup."  That
   method is not the one used here (NO [Cartesian] HYPOTHESIS, below).
   The same section (book p. 126, PDF
   p. 135) defines the intersection of two subobjects as their pullback,
   which Theory/Subobject/Lattice.v carries as [sub_meet] (#445).  nLab's
   "disjoint coproduct" names the general property: a coproduct is
   disjoint when its coprojections are monic and their pullback is
   initial.  This file proves that property, in the subobject form Mac Lane
   asks for, for EVERY binary coproduct in a category with a zero object
   and pullbacks -- the group statement is its instance at [Grp]
   (Instance/Grp/Colimit.v's [Grp_free_product_meet_trivial]).

   ** WHAT IS CONSUMED

   Structure/Bicartesian/Matrix.v's [inl_Monic] and [inr_Monic] (each
   injection is split by the copairing of the identity with the zero
   morphism), Theory/Subobject/Lattice.v's [sub_meet], [sub_bot],
   [sub_bot_least] and [sub_le_antisym], Structure/ZeroObject.v's
   [zero_mor] with [zero_mor_left] and [zero_mor_right], and
   Structure/Cocartesian.v's [inl_merge] and [inr_merge].

   ** WHAT IS BUILT

   [zero_initial_monic]: the arrow out of a zero object is monic, since
   its domain is also terminal.  [sub_inl], [sub_inr]: the two summands as
   subobjects of x + y.  [coprod_bot]: the bottom subobject of x + y,
   Lattice.v's [sub_bot] at the zero object.  [inl_pullback_leg_zero] and
   [inr_pullback_leg_zero]: both legs of the chosen pullback of the
   injections are zero morphisms -- apply the retraction [id ▽ zero_mor]
   (respectively [zero_mor ▽ id]) to the commuting square.
   [coproduct_injections_meet_trivial]: the meet of the two injections is
   the bottom subobject, [sub_meet sub_inl sub_inr ≈ coprod_bot].
   [coproduct_injections_pullback_zero]: the pullback of the injections is
   isomorphic to the zero object -- nLab's form -- read off the
   isomorphism of domains the subobject equivalence carries.

   NO [Cartesian] HYPOTHESIS.  The exercise's own method, the product
   G × H, is in this library Structure/Semiadditive.v's comparison map
   [can_comparison] from x + y to x × y, whose composites with the
   injections are [id △ zero_mor] and [zero_mor △ id]; it is the route
   the scouting prototype for this file took, and it assumes products as
   well.  It is deliberately NOT followed: the retraction alone suffices,
   and the theorem is stated over [ZeroObject], [Cocartesian] and
   [HasPullbacks] only: measured by [About], its binders are [C], [Z],
   [CC], [PB], [x] and [y], with no [Cartesian] among them.  (Issue #450's
   text asks for the two properties, listing generated subgroups and
   #445's subobject intersection as what they need, and does not mention
   the product: the product route is the book's hint, not the issue's.)

   ** STRENGTHS, STRICTEST FIRST

   The meet is NOT the bottom subobject on the nose: measured in a scratch
   file, [Example e : sub_meet (sub_inl x y) (sub_inr x y) = coprod_bot x y
   := eq_refl] is refused with "cannot unify "sub_meet (sub_inl x y)
   (sub_inr x y)" and "coprod_bot x y"" -- the two domains are the chosen
   pullback and the zero object, distinct objects.  The theorem is `≈` in
   the setoid of subobjects, which is an isomorphism of domains commuting
   with the monos; it ends in [Defined], so that isomorphism is the data
   [coproduct_injections_pullback_zero] projects.  The two leg lemmas are
   `≈` of morphisms.

   ** UNIVERSES, MEASURED

   By [About] under [Set Printing Universes], dropping bounds on stdlib
   globals: [zero_initial_monic@{u u0}], [sub_inl@{u u0}],
   [sub_inr@{u u0}], [coprod_bot@{u u0}] and the two leg lemmas are over
   [Category@{u u0 u0}] with EMPTY constraint blocks; the theorem and its
   corollary are [@{u u0 u1 u2}] with [u0 < u2], [u <= u1] and [u0 <= u1],
   the extra two universes being those of Lattice.v's subobject order
   ([sub_le_antisym@{u u0 u1 u2}] carries the same three constraints).  The
   identification of hom and proof universes is Lattice.v's ([sub_meet]
   is over [Category@{u u0 u0}] there), not this file's.

   ** THE COST OF REUSING [inl_Monic]

   Structure/Bicartesian/Matrix.v requires Category.Instance.Coq, so the
   dependency closure of this file, measured by iterating the build's
   coqdep output (.Makefile.coq.d) to a fixed point and counting modules
   OTHER than the file itself, is 75 modules against
   Theory/Subobject/Lattice.v's 48.  Of the 75, 27 are outside Lattice.v's
   closure; one of them is Lattice.v itself, and each of the other 26
   lies in Matrix.v's closure counted with Matrix.v included.  That is
   the price of not writing the two retractions a second time; Lattice.v
   itself requires neither Matrix.v nor Structure/ZeroObject.v, which is
   why this is a new file and not an appendix to it.

   ** NON-VACUITY

   Instance/Grp/Colimit.v instantiates the theorem at [Grp], at the
   coproduct the adjoint functor theorem produces, with Instance/Grp.v's
   [Grp_Zero] -- usable there since #450 wrote out that constant's
   universes -- and exhibits a nontrivial coproduct (the AFT coproduct of
   Z/2 with itself).

   ** AXIOMS

   Every constant of this file reports "Closed under the global context".

   ** NOT DELIVERED

   No version for categories without a zero object.  In [Sets] the
   pullback of the two injections is the empty set, but there is no
   retraction of [inl] out of x + y when x is empty and y is not, so the
   argument here does not apply and a different one (through a strict
   initial object; Lattice.v's [zero_monic_of_strict] is its first step)
   is not made.  No indexed or n-ary form.  No
   converse, and no statement that disjointness characterizes anything.
   No image factorization is used or needed: the injections are monic, so
   each is its own image.

--------
nLab：https://ncatlab.org/nlab/show/disjoint+coproduct
nLab：https://ncatlab.org/nlab/show/zero+object
nLab：https://ncatlab.org/nlab/show/subobject
维基百科：https://en.wikipedia.org/wiki/Free_product

麦克莱恩，《为工作中的数学家准备的范畴论》，第2版（GTM 5），§V.7 练习 1（书第128页，PDF第137页）要求，对于两个群的自由积，其两个注入映射是单射，并且它们的像在平凡子群中相交，并给出了一个方法。仓库目录中该练习的陈述摘要（doc/plan/books/maclane/inventory/V.json，条目 maclane:V.7:ex1，书第128页）在这一半的内容中写道：“还可以使用积 G x H，证明两个余积注入 G -> G + H 和 H -> G + H 是单射，并且它们的像在恒等子群中相交。”该方法并不是这里使用的方法（下面没有 [Cartesian] 假设）。同一节（书第126页，PDF第135页）将两个子对象的交定义为它们的拉回，而 Theory/Subobject/Lattice.v 将其作为 [sub_meet]（#445）表示。
nLab 的“析合余积”指一般性质：当余积的余投射是单射且它们的拉回为初始对象时，该余积是析合的。此文件证明了这个性质，以亚对象的形式——正如 Mac Lane 所要求的——适用于在具有零对象和拉回的范畴中的每一个二元余积——群论中的陈述是在 [Grp] 的实例（Instance/Grp/Colimit.v 的 [Grp_free_product_meet_trivial]）。

** 消耗的是什么

Structure/Bicartesian/Matrix.v 的 [inl_Monic] 和 [inr_Monic]（每个注入都通过同一性与零态射的共配对进行拆分）、Theory/Subobject/Lattice.v 的 [sub_meet]、[sub_bot]、[sub_bot_least] 和 [sub_le_antisym]、Structure/ZeroObject.v 的 [zero_mor] 与 [zero_mor_left] 和 [zero_mor_right]，以及 Structure/Cocartesian.v 的 [inl_merge] 和 [inr_merge]。

** 建造的是什么

[zero_initial_monic]：从零对象出的箭头是单射，因为它的定义域也是终对象。[sub_inl]，[sub_inr]：作为 x + y 的子对象的两个直和。[coprod_bot]：x + y 的底部子对象，Lattice.v 中零对象的 [sub_bot]。[inl_pullback_leg_zero] 和 [inr_pullback_leg_zero]：所选注入的拉回的两条腿都是零态射——将重traction [id ▽ zero_mor]（分别 [zero_mor ▽ id]）应用到交换方形。[coproduct_injections_meet_trivial]：两个注入的交是底部子对象 [sub_meet sub_inl sub_inr ≈ coprod_bot]。[coproduct_injections_pullback_zero]：注入的拉回同构于零对象——nLab 的形式——根据子对象等价所携带的定义域同构读出。

没有 [Cartesian] 假设。该练习自身的方法，即积 G × H，在此库 Structure/Semiadditive.v 的比较映射 [can_comparison] 中，从 x + y 映射到 x × y，其与注入的复合为 [id △ zero_mor] 和 [zero_mor △ id]；这是此文件原型勘探所采取的路线，并且它也假设了积。它是故意不遵循的：仅回退就足够了，并且定理仅在 [ZeroObject]、[Cocartesian] 和 [HasPullbacks] 上陈述：以 [About] 测量，其绑定器为 [C]、[Z]、[CC]、[PB]、[x] 和 [y]，且其中没有 [Cartesian]。（第450号问题的文本要求这两个性质，列出了生成子群和第445号问题的子对象交集作为它们所需的内容，并未提及积：积路线是书中的提示，而不是问题本身。）

** 优势，从最严格的开始

交会不是鼻子上的底部子对象：在一个 scratch 文件中测量时，[Example e : sub_meet (sub_inl x y) (sub_inr x y) = coprod_bot x y := eq_refl] 被拒绝，提示“无法统一 'sub_meet (sub_inl x y) (sub_inr x y)' 和 'coprod_bot x y'”——两个域分别是选择的拉回和零对象，是不同的对象。该定理是子对象集合（setoid）中的 `≈`，它是与单态（monos）可交换的域同构；它以 [Defined] 结束，因此该同构就是 [coproduct_injections_pullback_zero] 投影的数据。两个支引理是态射的 `≈`。

** 宇宙，已测量

由 [About] 在 [Set Printing Universes] 下，放宽 stdlib 的限制
   全局变量：[zero_initial_monic@{u u0}]、[sub_inl@{u u0}]、
   [sub_inr@{u u0}]、[coprod_bot@{u u0}] 和两个腿引理是在
   [Category@{u u0 u0}] 上使用 EMPTY 约束块完成的；该定理及其
   推论是在 [@{u u0 u1 u2}] 上使用 [u0 < u2]、[u <= u1] 和 [u0 <= u1] 完成的，
   额外的两个宇宙是 Lattice.v 的子对象顺序的宇宙
   （[sub_le_antisym@{u u0 u1 u2}] 承载相同的三个约束）。
   hom 和 proof 宇宙的识别是 Lattice.v 的（[sub_meet]
   在那里是 [Category@{u u0 u0}] 上的），而不是本文件的。

** 重用 [inl_Monic] 的成本

Structure/Bicartesian/Matrix.v 需要 Category.Instance.Coq，因此通过迭代构建的 coqdep 输出（.Makefile.coq.d）到固定点并计算除了文件本身之外的模块数来衡量的此文件的依赖闭包为75个模块，而 Theory/Subobject/Lattice.v 为48个。在这75个模块中，有27个不在 Lattice.v 的闭包中；其中一个是 Lattice.v 本身，其余26个都在包括 Matrix.v 在内计算的 Matrix.v 闭包中。这就是不重复编写两次收缩的代价；Lattice.v 本身不需要 Matrix.v 或 Structure/ZeroObject.v，这也是为什么这是一个新文件而不是它的附录。

** 非空性

Instance/Grp/Colimit.v 在 [Grp] 处实例化了该定理，在该处，余积由伴随定理生成，并与 Instance/Grp.v 的 [Grp_Zero] 一起使用 —— 因为 #450 已经写出了该常数的宇宙 —— 并展示了一个非平凡的余积（Z/2 与自身的 AFT 余积）。

** 公理

此文件的每个常量都报告“在全局上下文下关闭”

**未送达

对于没有零对象的范畴，没有版本。在 [Sets] 中，两个单射的拉回是空集，但当 x 为空且 y 不为空时，没有 [inl] 从 x + y 的重traction，所以这里的论证不适用，需要不同的论证（通过严格初始对象；Lattice.v 的 [zero_monic_of_strict] 是其第一步）并未给出。没有索引或 n 元形式。没有逆命题，也没有说明不相交可以表征任何东西。没有使用或需要图像分解：这些单射都是单态，所以每个单射都是其自身的图像。
*)

(** ** The arrow out of a zero object is monic / ** 从零对象出的箭头是单的 *)

Section ZeroMonic.

Context {C : Category}.
Context `{Z : @ZeroObject C}.

(*
Two arrows into the zero object agree because the zero object is also
   terminal; carrying them across the coincidence isomorphism makes that
   visible, and the cancellation hypothesis of [Monic] is never used.

--------
两个箭头指向零对象是一致的，因为零对象也是终对象；将它们通过重合同构进行转换可以使这一点显而易见，并且从未使用 [Monic] 的消去假设。
*)
Lemma zero_initial_monic (w : C) : Monic (@zero C (@zero_initial C Z) w).
Proof.
  constructor; intros v g1 g2 _.
  transitivity (from (@zero_coincide C Z) ∘ (to (@zero_coincide C Z) ∘ g1)).
  - rewrite comp_assoc, iso_from_to; cat.
  - transitivity (from (@zero_coincide C Z) ∘ (to (@zero_coincide C Z) ∘ g2)).
    + apply compose_respects; [reflexivity|].
      apply (@one_unique C (@zero_terminal C Z)).
    + rewrite comp_assoc, iso_from_to; cat.
Qed.

End ZeroMonic.

(** ** The two injections of a coproduct meet in the bottom subobject / ** 乘积的两个注入在底子对象中相交 *)

Section CoproductMeet.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CC : @Cocartesian C}.
Context `{PB : @HasPullbacks C}.
Context (x y : C).

(*
The two summands as subobjects of the coproduct, monic by
   Structure/Bicartesian/Matrix.v's [inl_Monic] and [inr_Monic].

--------
作为余积的子对象的两个加数，通过 Structure/Bicartesian/Matrix.v 的 [inl_Monic] 和 [inr_Monic] 是单射的。
*)
Definition sub_inl : SubObj (x + y) :=
  {| sub_dom := x; sub_mono := inl; sub_is_monic := inl_Monic x y |}.

Definition sub_inr : SubObj (x + y) :=
  {| sub_dom := y; sub_mono := inr; sub_is_monic := inr_Monic x y |}.

(*
The bottom subobject of the coproduct: the zero object, included by the
   arrow out of it.

--------
余积的底部子对象：零对象，由它发出的箭头包含。
*)
Definition coprod_bot : SubObj (x + y) :=
  @sub_bot C (@zero_initial C Z) (x + y) (zero_initial_monic (x + y)).

(*
Each leg of the chosen pullback of the two injections is the zero
   morphism: apply the retraction [id ▽ zero_mor] (resp. [zero_mor ▽ id])
   to the commuting square.

--------
所选两次注射的每一条回撤线都是零态射：将重traction [id ▽ zero_mor]（分别为 [zero_mor ▽ id]）应用到交换图上。
*)
Lemma inl_pullback_leg_zero :
  pullback_fst _ _ (pullback (@inl C CC x y) (@inr C CC x y)) ≈ zero_mor.
Proof.
  set (P := pullback (@inl C CC x y) (@inr C CC x y)).
  transitivity ((@id C x ▽ @zero_mor C Z y x) ∘ inl ∘ pullback_fst _ _ P).
  - rewrite inl_merge; cat.
  - rewrite <- comp_assoc, (pullback_commutes _ _ P), comp_assoc, inr_merge.
    apply zero_mor_right.
Qed.

Lemma inr_pullback_leg_zero :
  pullback_snd _ _ (pullback (@inl C CC x y) (@inr C CC x y)) ≈ zero_mor.
Proof.
  set (P := pullback (@inl C CC x y) (@inr C CC x y)).
  transitivity ((@zero_mor C Z x y ▽ @id C y) ∘ inr ∘ pullback_snd _ _ P).
  - rewrite inr_merge; cat.
  - rewrite <- comp_assoc, <- (pullback_commutes _ _ P), comp_assoc,
      inl_merge.
    apply zero_mor_right.
Qed.

Theorem coproduct_injections_meet_trivial :
  sub_meet sub_inl sub_inr ≈ coprod_bot.
Proof.
  apply sub_le_antisym.
  - exists (from (@zero_coincide C Z) ∘ @one C (@zero_terminal C Z) _).
    simpl.
    rewrite inl_pullback_leg_zero, zero_mor_left.
    unfold zero_mor; rewrite comp_assoc; reflexivity.
  - apply sub_bot_least.
Defined.

(*
The same fact in nLab's form: the pullback of the two injections is the
   zero object, read off the isomorphism the subobject equivalence
   carries.

--------
在 nLab 的形式中相同的事实：两个单射的拉回是零对象，从同构中可以得出子对象等价所承载的内容。
*)
Definition coproduct_injections_pullback_zero :
  Pull (@inl C CC x y) (@inr C CC x y) (pullback inl inr)
    ≅ @initial_obj C (@zero_initial C Z) :=
  `1 coproduct_injections_meet_trivial.

End CoproductMeet.
