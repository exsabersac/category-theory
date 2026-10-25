Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * The cokernel pair of [Sets] is a cokernel pair / * * [Sets] 的余核对是一个余核对 *)

(*
 nLab: https://ncatlab.org/nlab/show/cokernel+pair

 Mac Lane, CWM 2nd ed., §III.3 p. 66 and §III.4 Exercise 4 p. 72; Fong
 and Spivak, *Seven Sketches*, §7.2.1 Definition 7.5.

 Instance/Sets.v already builds, for f : A ~> B in [Sets], the
 setoid [CKSetoid f] — two copies of B glued exactly along the image of
 f — with two inclusions [ck_left]/[ck_right] and the equation
 [ck_agree : ck_left ∘ f ≈ ck_right ∘ f].  It was built to probe an
 epimorphism, and it stops there: NO universal property of it is proved
 in that file, the word "pushout" occurs there only in an
 unrelated header line, and it is nowhere related to
 Instance/Sets/Pushout.v's [Sets_HasPushouts], which sits in a different
 file and glues by a five-constructor inductive closure instead.

 This file proves the universal property, so that the pre-existing
 construction is exhibited as a genuine cokernel pair —
 [sets_ck_IsCokernelPair] — and hence as a pushout square in the sense
 of Theory/Morphisms/CokernelPair.v.  Nothing in Instance/Sets.v is
 changed; the mediator is the copairing of the two competing maps, and
 the ONLY step with content is its respectfulness at the gluing case,
 where the image witness supplies the preimage that lets the coequalizing
 hypothesis be applied.  As everywhere in [Sets], `∃` is [sigT], so that
 preimage is DATA and no choice principle is used.

 ------------------------------------------------------------------
 ** What is proved, and at what strength

 - [sets_ck_ump], [sets_ck_IsCokernelPair]: the universal property, and
 the apex-pinned identification.  The two triangles hold POINTWISE ON
 THE NOSE — [sets_ck_med_left]/[sets_ck_med_right] are [reflexivity]
 at every point, the mediator being defined by case analysis on the
 sum — and this is recorded as two [eq_refl] Examples on the
 underlying FUNCTIONS ([sets_ck_med_inl], [sets_ck_med_inr]).  What
 does NOT hold strictly is the equality of MORPHISMS: the composite
 [u ∘ ck_left] rebuilds its [proper_morphism] certificate, so the
 triangles are [≈] and not [eq].  That negative is pinned in
 Test/ProbeCokernelPair.v.

 - Non-vacuity BOTH WAYS, on Instance/Sets.v's own two-element witness
 pair, so that neither side of the characterization is empty:

 * [collapse : bool ~> unit] is surjective, hence epic, and its
 cokernel-pair legs are proved to agree
 ([sets_collapse_ckp_trivial]), so the identity square on it IS a
 pushout ([sets_collapse_pushout_square]).

 * [pick_true : unit ~> bool] misses [false], and its cokernel-pair
 legs are proved DISTINCT by hand ([sets_pick_true_ckp_nontrivial])
 — at [false] the gluing relation would demand a preimage, i.e.
 [true = false].  Hence the identity square on it is NOT a pushout
 ([sets_pick_true_not_pushout_square]).

 The second witness is the load-bearing one: it is what shows the
 general biconditional is not vacuously true, and it CROSS-CHECKS the
 general theory — [sets_pick_true_not_epic_via_ckp] re-derives
 Instance/Sets.v's [pick_true_not_epic] from the distinctness of the
 legs through [epic_iff_cokernel_pair_trivial], by a route that shares
 no proof text with the original.

 ------------------------------------------------------------------
 ** Universes, measured in the constraint blocks

 [sets_ck_IsCokernelPair@{h p}] and [sets_ck_ump@{h p}] carry two
 universe parameters.  Beyond [Sets]'s own [p < h] ([Sets@{o so} :
 Category@{so o o}] with [o < so], the carriers at [o]) the block records
 only bounds INHERITED verbatim — [p <= compose.u0], [p <= compose.u1],
 [p <= compose.u2], [p <= ID.u0], each of which [Sets], [CKSetoid],
 [ck_left] and [ck_agree] display identically.  (An earlier draft called
 [p < h] "the single constraint"; there are five lines.  The substance is
 unaffected: nothing here narrows the shape, and the identification is
 polymorphic in the carrier universe [p].)

 The two-element WITNESSES do pin, and only they:
 [sets_pick_true_not_pushout_square@{u}] displays
 [bool_setoid_object@{Set Set}] with [Set < u], because
 Instance/Sets.v's [bool_setoid_object] has a [bool] carrier.  That is
 the ordinary concrete-witness price and it is confined to the
 non-vacuity section.

 ------------------------------------------------------------------
 ** NOT DELIVERED (scoped)

 - [CKSetoid f] is NOT identified with the chosen pushout of
 [Sets_HasPushouts] (Instance/Sets/Pushout.v).  The two are different
 objects — a closed-form relation against an inductive closure — and
 the comparison would need a general "any two pushouts of one span are
 uniquely isomorphic" statement, which Theory/Morphisms/CokernelPair.v
 deliberately does not provide.  No claim is made here about whether
 they are isomorphic; the question is simply not addressed.

 - The [Top] and pointed-sets cokernel pairs (Instance/Top.v,
 Instance/Sets/Pointed.v) are NOT given universal properties.
 Only the [Sets] one is treated here.

 - No [Sets]-specific statement about [Monic] and kernel pairs. 

 --------
 nLab: https://ncatlab.org/nlab/show/cokernel+pair

 Mac Lane, CWM 第二版, §III.3 第66页 和 §III.4 练习4 第72页; Fong 和 Spivak, *七个素描*, §7.2.1 定义7.5.

 Instance/Sets.v 已经为 f : A ~> B 在 [Sets] 中构建了集合等价 [CKSetoid f] — 两个 B 的副本正好沿 f 的像粘合 — 并带有两个包含映射 [ck_left] / [ck_right] 以及方程 [ck_agree : ck_left ∘ f ≈ ck_right ∘ f]。它是为了探测一个满射而构建的，并且止步于此：在该文件中没有证明其任何普遍性质，单词“pushout”仅在一个无关的标题行中出现，并且与 Instance/Sets/Pushout.v 中的 [Sets_HasPushouts] 没有任何关系，后者位于不同文件中，并通过五构造子归纳闭包进行粘合。此文件证明了泛性质，因此预先存在的构造被展示为真正的余核对——[sets_ck_IsCokernelPair]——因此在Theory/Morphisms/CokernelPair.v的意义上是一个推出方格。Instance/Sets.v中的内容没有任何改变；中介者是两个竞争映射的合对映射，唯一有实际内容的步骤是在粘合情况中其守恒性，此时图像证据提供了允许应用共等化假设的原像。正如在[Sets]中的各处，`∃`是[sigT]，因此原像是数据，并未使用任何选择公理。

 ------------------------------------------------------------------
 ** 证明了什么，以及证明的强度是什么- [sets_ck_ump], [sets_ck_IsCokernelPair]：泛性质，以及顶点固定的识别。这两个三角形在鼻子处逐点成立——[sets_ck_med_left] / [sets_ck_med_right]在每个点上都是[reflexivity]，中介由对和的情况分析定义——这被记录为基础函数（[sets_ck_med_inl], [sets_ck_med_inr]）上的两个[eq_refl]例子。严格来说不成立的是态射的相等性：复合[u ∘ ck_left]重建了它的[proper_morphism]证书，因此三角形是[≈]而不是[eq]。这个否定被固定在Test/ProbeCokernelPair.v中。

 - 双向非空，在Instance/Sets.v自身的两个元素见证对上，因此特征化的任一方都不为空：*  [collapse : bool ~> unit] 是满射，因此是史诗态（epic），并且其余核对（cokernel-pair）枝被证明一致（[sets_collapse_ckp_trivial]），所以它上的恒等方形是一个推出图（pushout）（[sets_collapse_pushout_square]）。

 *  [pick_true : unit ~> bool] 缺少 [false]，并且其余核对枝被人工证明为不同（[sets_pick_true_ckp_nontrivial]）—— 在 [false]，粘合关系将要求一个原像，即 [true = false]。因此它上的恒等方形不是一个推出图（[sets_pick_true_not_pushout_square]）。

 第二个例子是关键的：它显示了一般的双条件并非空洞成立，并且它交叉验证了总体理论—— [sets_pick_true_not_epic_via_ckp] 通过 [epic_iff_cokernel_pair_trivial]，从枝的不同性重新推导了 Instance/Sets.v 中的 [pick_true_not_epic]，这一路径与原始证明文本没有共享。------------------------------------------------------------------
 ** 宇宙，在约束块中测量

 [sets_ck_IsCokernelPair@{h p}] 和 [sets_ck_ump@{h p}]  携带两个
 宇宙参数。超出 [Sets] 自身的 [p < h] ([Sets@{o so} :
 Category@{so o o}] 与 [o < so], 在 [o] 的承载体) 该块仅记录
 逐字继承的界限——[p <= compose.u0], [p <= compose.u1],
 [p <= compose.u2], [p <= ID.u0]，每个 [Sets], [CKSetoid],
 [ck_left] 和 [ck_agree] 显示相同。(早期草稿将
 [p < h] 称为“单一约束”；共有五行。实质
 未受影响：此处没有任何东西缩小形状，并且在承载宇宙 [p] 中识别是多态的。)两个元素的证人确实标记，并且只有它们：
 [sets_pick_true_not_pushout_square@{u}] 显示
 [bool_setoid_object@{Set Set}] 使用 [Set < u]，因为
 Instance/Sets.v 的 [bool_setoid_object] 有一个 [bool] 载体。那是普通的具体证人价格，并且它仅限于非空部分。

 ------------------------------------------------------------------
 ** 未交付（有范围）- [CKSetoid f] 并未与所选的 [Sets_HasPushouts]（Instance/Sets/Pushout.v）推出来的对象相识别。两者是不同的对象——一个是闭式关系，一个是归纳闭包——而其比较需要一个通用的“同一跨度的任何两个推对象都是唯一同构的”声明，而 Theory/Morphisms/CokernelPair.v 故意没有提供该声明。这里没有关于它们是否同构的主张；这个问题根本没有被讨论。

 - [Top] 和有指向集的余核对（Instance/Top.v, Instance/Sets/Pointed.v）没有给出普遍性质。这里只处理了 [Sets] 的那一个。

 - 没有关于 [Sets] 的 [Monic] 和核对的特定声明。
*)

Section SetsCokernelPair.

Universes h p.
Context {A B : SetoidObject@{p p}}.
Context (f : A ~{Sets@{p h}}~> B).

(** ** The mediator / ** 调解员 *)

(* The copairing of two competing maps: on the left copy use q1, on the right copy use q2. / 两个竞争映射的协配：左边副本使用 q1，右边副本使用 q2。 *)
Definition sets_ck_fun {Q : SetoidObject@{p p}}
           (q1 q2 : B ~{Sets@{p h}}~> Q)
  : carrier (CKSetoid f) → carrier Q :=
  λ s, match s with
       | Datatypes.inl b => q1 b
       | Datatypes.inr b => q2 b
       end.

(*
 Respectfulness.  Three of the four cases are [proper_morphism] of q1 or
 q2; the two GLUING cases are the whole content, and they are where the
 coequalizing hypothesis is spent: the image witness names a preimage
 [a] with [f a ≈ x], at which [q1] and [q2] agree by hypothesis. 

 --------
 尊重。四个案例中有三个是 q1 或 q2 的 [proper_morphism]；两个 GLUING 案例是整个内容所在，它们是协同化假设被使用的地方：像证人命名了一个前像 [a] 与 [f a ≈ x]，在该处 [q1] 和 [q2] 根据假设一致。
*)
Lemma sets_ck_respects {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f)
      (s t : carrier (CKSetoid f)) :
  ckrel f s t → sets_ck_fun q1 q2 s ≈ sets_ck_fun q1 q2 t.
Proof.
  destruct s as [xs|xs], t as [xt|xt]; simpl.
  - intro E; now rewrite E.
  - intros [E [a Ha]].
    (* q1 xs ≈ q1 (f a) ≈ q2 (f a) ≈ q2 xs ≈ q2 xt / q1 xs ≈ q1 (f a) ≈ q2 (f a) ≈ q2 xs ≈ q2 xt *)
    transitivity (q1 (f a)); [ now rewrite Ha |].
    transitivity (q2 (f a)); [ exact (Hc a) |].
    rewrite Ha; now rewrite E.
  - intros [E [a Ha]].
    transitivity (q2 (f a)); [ now rewrite Ha |].
    transitivity (q1 (f a)); [ symmetry; exact (Hc a) |].
    rewrite Ha; now rewrite E.
  - intro E; now rewrite E.
Qed.

Program Definition sets_ck_med {Q : SetoidObject@{p p}}
        (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f)
  : CKSetoid f ~{Sets@{p h}}~> Q :=
  {| morphism := sets_ck_fun q1 q2 |}.
Next Obligation.
  repeat intro; now apply sets_ck_respects.
Qed.

(** ** The universal property / ** 通用性质 *)

(* Both triangles are POINTWISE [reflexivity]: the mediator is defined by case analysis on the sum, and each leg lands in exactly one case. / 两个三角形在点上都是 [reflexivity]：中介通过对总和进行情况分析来定义，每条边恰好落在一个情况中。 *)
Lemma sets_ck_med_left {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  sets_ck_med q1 q2 Hc ∘[Sets@{p h}] ck_left f ≈ q1.
Proof. intro b; reflexivity. Qed.

Lemma sets_ck_med_right {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  sets_ck_med q1 q2 Hc ∘[Sets@{p h}] ck_right f ≈ q2.
Proof. intro b; reflexivity. Qed.

Lemma sets_ck_ump (Q : SetoidObject@{p p})
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  ∃! u : CKSetoid f ~{Sets@{p h}}~> Q,
    u ∘[Sets@{p h}] ck_left f ≈ q1 ∧ u ∘[Sets@{p h}] ck_right f ≈ q2.
Proof.
  unshelve refine {| unique_obj := sets_ck_med q1 q2 Hc |}.
  - split; [ apply sets_ck_med_left | apply sets_ck_med_right ].
  - intros v [Hv1 Hv2] s.
    destruct s as [b|b]; simpl.
    + symmetry; exact (Hv1 b).
    + symmetry; exact (Hv2 b).
Qed.

(* Instance/Sets.v's construction IS a cokernel pair. The commuting equation is that file's own [ck_agree], reused rather than reproved. / Instance/Sets.v 的构造确实是一个余核对。交换方程是该文件自身的 [ck_agree]，重复使用而不是重新证明。 *)
Definition sets_ck_IsCokernelPair
  : IsCokernelPair (C:=Sets@{p h}) f (CKSetoid f) (ck_left f) (ck_right f) :=
  @Build_IsPushoutSquare Sets@{p h} A B B f f
    (CKSetoid f) (ck_left f) (ck_right f) (ck_agree f) sets_ck_ump.

End SetsCokernelPair.

(* * ** The two triangles hold on the nose on the underlying functions / * ** 两个三角形正好对应在底层函数上 *)

(*
 The mediator's value at either injection is the corresponding competing
 map applied to the point — Leibniz, not merely [≈].  What is NOT strict
 is the equality of MORPHISMS (see Test/ProbeCokernelPair.v). 

 --------
 在任一注入时，中介者的值是相应的竞争映射作用于该点——莱布尼茨，而不仅仅是 [≈]。严格性不适用的是 MORPHISMS 的等式（见 Test/ProbeCokernelPair.v）。
*)
Example sets_ck_med_inl@{h p} {A B Q : SetoidObject@{p p}}
        (f : A ~{Sets@{p h}}~> B) (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) (b : carrier B) :
  sets_ck_med f q1 q2 Hc (Datatypes.inl b) = q1 b := eq_refl.

Example sets_ck_med_inr@{h p} {A B Q : SetoidObject@{p p}}
        (f : A ~{Sets@{p h}}~> B) (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) (b : carrier B) :
  sets_ck_med f q1 q2 Hc (Datatypes.inr b) = q2 b := eq_refl.

(** ** Non-vacuity, both ways / ** 非空，两方面 *)

(*
 Instance/Sets.v's own witness pair between the singleton and the
 two-element setoid is used, so no new object is introduced. 

 --------
 Instance/Sets.v 自己在单元素集合与双元素集合之间的见证对被使用，因此没有引入新的对象。
*)

(* * *** The epic side: [collapse] is surjective, so its legs agree / * *** 史诗般的一面：[collapse] 是满射的，所以它的腿是一致的 *)

Lemma sets_collapse_surjective :
  ∀ u : carrier unit_setoid_object, ∃ b, collapse b ≈ u.
Proof. intro u; exists true; destruct u; reflexivity. Qed.

Definition sets_collapse_epic : Epic collapse :=
  surjective_implies_epic collapse sets_collapse_surjective.

(*
 Its cokernel pair is trivial: the two legs of [CKSetoid collapse]
 coincide.  Obtained through the general theorem, not by computation. 

 --------
 它的余核对是平凡的：[CKSetoid collapse] 的两条支线重合。通过一般定理得到，而不是通过计算得到的。
*)
Definition sets_collapse_ckp_trivial :
  ck_left collapse ≈ ck_right collapse :=
  fst (epic_iff_cokernel_pair_trivial (C:=Sets) collapse
         (is_pushout_square_pushout (sets_ck_IsCokernelPair collapse)))
      sets_collapse_epic.

(* And the identity square on it is a pushout. / 并且它上的恒等方是一个推出图。 *)
Definition sets_collapse_pushout_square :
  IsPushoutSquare (C:=Sets) collapse collapse unit_setoid_object id id :=
  fst (epic_iff_pushout_square collapse) sets_collapse_epic.

(* * *** The non-epic side: [pick_true] misses [false] / * *** 非史诗一方：[pick_true] 想念 [false] *)

(*
 The two legs of [CKSetoid pick_true] are DISTINCT, proved by hand: at
 [false] the gluing relation would supply a preimage of [false] under
 [pick_true], i.e. a proof that [true = false]. 

 --------
 [CKSetoid pick_true] 的两条腿是不同的，通过手工证明：在 [false] 处，粘合关系会提供 [false] 在 [pick_true] 下的逆像，也就是 [true = false] 的证明。
*)
Lemma sets_pick_true_ckp_nontrivial :
  ck_left pick_true ≈ ck_right pick_true → False.
Proof.
  intro E.
  (*
 [E false] inhabits [ckrel pick_true (inl false) (inr false)], whose
 second component is the image witness. 

 --------
 [E false] 居住在 [ckrel pick_true (inl false) (inr false)]，其第二个组成部分是图像见证。
*)
  destruct (E false) as [_ [u Hu]].
  destruct u.
  exact (Bool.diff_true_false Hu).
Qed.

(*
 Hence the identity square on [pick_true] is NOT a pushout: were it one,
 [pick_true] would be epic and the legs would have to agree. 

 --------
 因此，[pick_true] 上的恒等方阵不是一个推挤图：如果它是的话，[pick_true] 将是一个满射，并且两边必须一致。
*)
Lemma sets_pick_true_not_pushout_square :
  IsPushoutSquare (C:=Sets) pick_true pick_true bool_setoid_object id id
  → False.
Proof.
  intro H.
  apply sets_pick_true_ckp_nontrivial.
  exact (fst (epic_iff_cokernel_pair_trivial (C:=Sets) pick_true
                (is_pushout_square_pushout
                   (sets_ck_IsCokernelPair pick_true)))
             (snd (epic_iff_pushout_square pick_true) H)).
Qed.

(*
 Cross-check: Instance/Sets.v's [pick_true_not_epic] re-derived through
 the general characterization, by a route sharing no proof text with the
 original (that one probes with [id] against [pick_true ∘ collapse];
 this one goes through the cokernel pair). 

 --------
 交叉检查：通过一般特征重新推导  Instance/Sets.v 的 [pick_true_not_epic]，采用的路径与原始路径没有共享的证明文本（原路径是用 [id] 对 [pick_true ∘ collapse] 进行探测；这一条路径则是通过余核对）。
*)
Lemma sets_pick_true_not_epic_via_ckp : Epic pick_true → False.
Proof.
  intro E.
  apply sets_pick_true_ckp_nontrivial.
  exact (fst (epic_iff_cokernel_pair_trivial (C:=Sets) pick_true
                (is_pushout_square_pushout
                   (sets_ck_IsCokernelPair pick_true))) E).
Qed.
