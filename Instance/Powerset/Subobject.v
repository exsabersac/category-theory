Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.

Generalizable All Variables.

(*
   * * The direct image and the preimage on SUBOBJECTS

   Seven Sketches (Fong and Spivak, "An Invitation to Applied Category
   Theory") §1.4.3.  There is no page image for that book here, so the
   two clauses are quoted from the catalog issue's own transcription:

   "the direct image ... as an operation on subobjects"

   "monotonicity of the subobject preimage"

   The second is a gap in the tree that can be stated precisely: the
   reindexing map [sub_reindex] of Theory/Subobject/Functor.v is
   proved to respect the [SubObj] SETOID ([sub_reindex_respects]),
   to be the identity at [id] and to turn composition into
   composition, but nothing anywhere says it is monotone for
   Theory/Subobject.v's ORDER [sub_le] -- measured: the token
   [sub_le] does not occur in Theory/Subobject/Functor.v at all.  That
   is [sub_reindex_monotone] below.

   nLab: https://ncatlab.org/nlab/show/subobject
   nLab: https://ncatlab.org/nlab/show/image
   nLab: https://ncatlab.org/nlab/show/base+change

   ** WHY NONE OF THIS GOES THROUGH [Proset]

   [sub_le u v] is [{ k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈
   sub_mono u }] -- a [sigT], hence [Type]-valued.  A [relation] is
   [Prop]-valued, so [sub_le] is not one, and neither
   Instance/Proset.v's [Proset] nor Instance/Proset/Galois.v's
   [GaloisConnection] can be applied to it.  This file therefore states
   everything elementarily, with no category of subobjects and no
   adjunction; Instance/Powerset.v's [Subsets] is the Prop-valued
   counterpart where those DO apply, and the last section relates the
   two.  (The same Type-versus-Prop wall is what keeps
   Instance/Sets/Powerset.v's proof-relevant [Powerset_obj] out of
   Instance/Powerset.v; that rejection is pinned as the probe's formability
   negative 2, a sort rejection.)

   ** WHAT IS DELIVERED, WITH GRADES

   (A) [sub_reindex_monotone], in ANY category with chosen pullbacks:
   the mediator into the chosen pullback of [sub_mono v] along [f],
   built from the [sub_le] factorization; its FIRST triangle IS the
   required [sub_le] equation, so the [sub_le] witness is read off
   [ump_pullbacks] with no further step.  General, so it mentions
   neither [Sets] nor images and is stated before them.  (The file
   still has [Instance/Sets] in scope, transitively, because
   Theory/Subobject/Functor.v itself requires it; that is the
   donor's import, not this section's.)

   (B) [sub_image] in [Sets]: the image of [f ∘ sub_mono u], with
   Instance/Sets/Image.v's [Sets_Image_mono] as the mono and
   [Sets_Image_mono_monic] as its monicity, both cited rather than
   reproved.  [sub_image_monotone] carries [sub_le] forward, and
   [sub_image_respects] upgrades that to the [SubObj] setoid --
   cheaply, because BOTH comparison maps preserve the first
   projection and the image setoid compares nothing else, so the two
   inverse laws are [reflexivity].

   (C) The transposition at subobject level, BOTH directions:
   [sub_image_transpose_to] and [sub_image_transpose_from],
   packaged as [sub_image_reindex_iffT].  The backward direction is
   the one with content: its comparison map sends an image point to
   the second pullback projection of the mediator, and its
   RESPECTFULNESS is where monicity of [sub_mono v] is spent --
   two image points with the same first projection may carry
   different preimages, and only injectivity of a mono in [Sets]
   (Instance/Sets.v's [injectivity_is_monic], backward leg)
   identifies their values.

   (D) The bridges to #311's passages, at [≈] (NOT at [eq_refl] -- the
   two truncated existentials are differently bracketed, which is
   exactly what each proof reassociates):
   [sub_image_is_Powerset_Prop_image] and
   [sub_reindex_is_Powerset_Prop_preimage].  With them,
   [subset_le_of_sub_le] carries the Type-valued subobject order to
   the Prop-valued subset order.

   ** WHAT IS NOT DELIVERED

   No category of subobjects, no [Proset], no adjunction and no Galois
   connection at this level -- see the wall above.  No claim that the
   two bridges are mutually inverse (#311 proves one composite,
   [Powerset_subset_roundtrip], and says in terms why the other is
   blocked).  No naturality of [sub_image] in [f], no functoriality in
   the subobject beyond the two monotonicity statements, no image
   factorization system, and nothing about [sub_le_monic] or
   [sub_le_unique] beyond citing them.

   ** UNIVERSES

   Section (A) is at whatever universes the ambient category has; (B)
   through (D) inherit [Set < o] from [Powerset_Prop_truth] as usual and
   [o < so] from [Sets@{o so}].  No constant here introduces a [Set]
   pin.  Measured per constant in the report.

   ** TRANSPARENCY

   [sub_image_map] and [sub_transpose_from_map] MUST be [Defined]:
   measured by flipping each to [Qed], which breaks the file, since the
   consumers read their underlying functions.  The other three
   [Defined]s here compile as [Qed] and are so written for uniformity.

   ** REGISTRATION

   Nothing is an [Instance] except [sub_image_respects], which is
   declared [#[export] Instance] to match Theory/Subobject/Functor.v's
   [sub_reindex_respects] -- the two are the same kind of fact about the
   same setoid, and a [Proper] instance is what setoid rewriting
   consumes. 

   --------
   * * 子对象上的直接像和原像

   《七个素描》（Fong 和 Spivak，《应用范畴理论导引》）§1.4.3。本书在此没有页面图片，因此以下两条引自目录期刊的自身转录：

   “直接像……作为子对象上的一种运算”

   “子对象原像的单调性”第二个是树中的一个空缺，可以精确地陈述：Theory/Subobject/Functor.v 的重索引映射 [sub_reindex] 被证明尊重 [SubObj] SETOID ([sub_reindex_respects])，在 [id] 时为恒等，并且将组合映射为组合，但没有任何地方说明它对 Theory/Subobject.v 的顺序 [sub_le] 是单调的——测量方法：在 Theory/Subobject/Functor.v 中根本没有出现标记 [sub_le]。这就是下面的 [sub_reindex_monotone]。

   nLab: https://ncatlab.org/nlab/show/subobject
   nLab: https://ncatlab.org/nlab/show/image
   nLab: https://ncatlab.org/nlab/show/base+change

   ** 为什么这些都不适用于 [Proset][sub_le u v] 是 [{ k : sub_dom u ~> sub_dom v & sub_mono v ∘ k ≈ sub_mono u }] —— 一个 [sigT]，因此是 [Type] 值的。一个 [relation] 是 [Prop] 值的，所以 [sub_le] 不是一个，并且 Instance/Proset.v 的 [Proset] 以及 Instance/Proset/Galois.v 的 [GaloisConnection] 都不能应用于它。因此，这个文件以最基本的方式说明了一切，没有子对象的范畴也没有陪伴；Instance/Powerset.v 的 [Subsets] 是可以应用这些的 Prop 值对应物，最后一节将二者关联。（同样的 Type 与 Prop 之墙也阻止了 Instance/Sets/Powerset.v 的证明相关 [Powerset_obj] 进入 Instance/Powerset.v；这一拒绝被确定为探针的可形成性负2，一种类型拒绝。）

   ** 所提供内容及等级(A) [sub_reindex_monotone]，在任意具有所选回退的范畴中：中介子进入沿 [f] 的 [sub_mono v] 所选回退，由 [sub_le] 因式分解构建；它的第一个三角形是所需的 [sub_le] 方程，因此 [sub_le] 见证可以从 [ump_pullbacks] 直接读出，无需进一步步骤。一般性地，它既没有提到 [Sets]，也没有提到像，并且在它们之前陈述。（该文件仍然在作用域内具有 [Instance/Sets]，作为传递，因为 Theory/Subobject/Functor.v 本身需要它；这是捐赠者的导入，而不是本节的。）(B) [sub_image] 在 [Sets] 中：[f ∘ sub_mono u] 的像，使用 Instance/Sets/Image.v 的 [Sets_Image_mono] 作为单态，[Sets_Image_mono_monic] 作为其单性，两者都是引用而非重新证明。[sub_image_monotone] 推进了 [sub_le]，并且 [sub_image_respects] 将其升级为 [SubObj] 集合套件——廉价的，因为两个比较映射都保持第一投影，并且像集合套件不比较其他任何东西，所以这两个逆定律是 [reflexivity]。(C) 子对象层次的置换，两个方向：
   [sub_image_transpose_to] 和 [sub_image_transpose_from]，
   打包为 [sub_image_reindex_iffT]。反向是
   含有内容的那个：它的比较映射将一个像点映射到中介的第二拉回投影，并且它的
   尊重性体现在 [sub_mono v] 的单射性上——
   两个具有相同第一投影的像点可能有不同的原像，只有 [Sets] 中单射的单射性
   （Instance/Sets.v 中的 [injectivity_is_monic]，反向分支）
   能够识别它们的值。(D) 通向 #311 段落的桥梁，在 [≈]（不是在 [eq_refl]——两个截断的存在式括号不同，这正是每个证明重新结合的内容）：
   [sub_image_is_Powerset_Prop_image] 和
   [sub_reindex_is_Powerset_Prop_preimage]。 有了它们，
   [subset_le_of_sub_le] 将类型值子对象顺序传递到命题值子集顺序。

   ** 未实现的内容没有子对象的类别，没有 [Proset]，没有伴随，也没有 Galois 连接——见上面的墙。没有声称这两座桥是互为逆的（#311 证明了一个复合 [Powerset_subset_roundtrip]，并在术语上说明为什么另一个被阻塞）。在 [f] 中没有 [sub_image] 的自然性，子对象中除了两个单调性陈述之外，没有函子性，没有像像分解系统，也没有关于 [sub_le_monic] 或 [sub_le_unique] 的内容，除了引用它们之外。

   ** 宇宙

   (A) 部分在环境类别所拥有的任意宇宙中；(B) 到 (D) 部分如常继承 [Set < o] 自 [Powerset_Prop_truth]，以及继承 [o < so] 自 [Sets@{o so}]。这里没有常量引入 [Set] 钉。按报告中的每个常量进行测量。

   ** 透明度[sub_image_map] 和 [sub_transpose_from_map] 必须是 [Defined] ：
   通过将每个翻转为 [Qed] 来测量，这会破坏文件，因为消费者会读取它们的底层函数。其他三个 [Defined] 在这里编译为 [Qed]，并且这样编写是为了统一。

   ** 注册

   除了 [sub_image_respects]，没有任何东西是 [Instance]，它被声明为 [#[export] 实例] 以匹配 Theory/Subobject/Functor.v 的 [sub_reindex_respects] —— 两者是关于同一个集合等价关系的相同类型的事实，而 [Proper] 实例是集合等价重写消耗的。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) The subobject preimage is monotone, in any category / * **（A）子对象的原像在任何范畴中都是单调的 *)

Section ReindexMonotone.

Context {C : Category}.
Context `{@HasPullbacks C}.

(*
 Given u ≤ v over x and f : y ~> x, the two chosen pullbacks compare.
 The competing square is the pullback of u corrected by the [sub_le]
 factorization [k], and the mediator's first triangle is exactly the
 [sub_le] equation required downstairs. 

 --------
 给定在 x 上 u ≤ v 以及 f : y ~> x，所选的两个拉回图进行比较。竞争的方形图是通过 [sub_le] 分解 [k] 校正的 u 的拉回图，而调解者的第一个三角形正是楼下所需的 [sub_le] 方程。
*)
Lemma sub_reindex_monotone {x y : C} (f : y ~> x) {u v : SubObj x} :
  sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v).
Proof.
  intros [k Hk].
  assert (Hsq : f ∘ pullback_fst f (sub_mono u) (pullback f (sub_mono u))
                  ≈ sub_mono v
                      ∘ (k ∘ pullback_snd f (sub_mono u)
                             (pullback f (sub_mono u)))).
  { rewrite comp_assoc, Hk.
    exact (pullback_commutes f (sub_mono u) (pullback f (sub_mono u))). }
  destruct (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
              (Pull f (sub_mono u) (pullback f (sub_mono u)))
              (pullback_fst f (sub_mono u) (pullback f (sub_mono u)))
              (k ∘ pullback_snd f (sub_mono u) (pullback f (sub_mono u)))
              Hsq) as [w [Hw1 Hw2] _].
  exact (existT _ w Hw1).
Defined.

End ReindexMonotone.

(* ------------------------------------------------------------------------ *)
(* * ** (B) The direct image of a subobject of a setoid / * **（B）集合等价类子对象的直接像 *)

Section SubImage.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(*
 The direct image of a subobject: the image of the composite mono,
 Instance/Sets/Image.v's construction reused whole. 

 --------
 子对象的直接像：复合单射的像，Instance/Sets/Image.v 的构造整体重用。
*)
Definition sub_image (u : @SubObj Sets@{o so} A) : @SubObj Sets@{o so} B :=
  @Build_SubObj Sets@{o so} B
    (Sets_Image (f ∘ sub_mono u))
    (Sets_Image_mono (f ∘ sub_mono u))
    (Sets_Image_mono_monic (f ∘ sub_mono u)).

(*
 The comparison map along a [sub_le] factorization: the same image
 point with its preimage transported through [k].  The membership
 witness is factored out so the map itself is a plain term. 

 --------
 沿着 [sub_le] 分解的比较映射：相同的图像点及其通过 [k] 传输的原像。成员资格证明被分解出去，所以映射本身是一个普通项。
*)
Lemma sub_image_witness {u v : @SubObj Sets@{o so} A}
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom v)
  (Hk : sub_mono v ∘ k ≈ sub_mono u)
  (p : carrier (Sets_Image (f ∘ sub_mono u))) :
  f (sub_mono v (k (`1 (`2 p)))) ≈ `1 p.
Proof.
  transitivity (f (sub_mono u (`1 (`2 p)))).
  - exact (proper_morphism f _ _ (Hk (`1 (`2 p)))).
  - exact (`2 (`2 p)).
Qed.

Definition sub_image_map {u v : @SubObj Sets@{o so} A}
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom v)
  (Hk : sub_mono v ∘ k ≈ sub_mono u) :
  sub_dom (sub_image u) ~{Sets@{o so}}~> sub_dom (sub_image v).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _ _ _ _
       (fun p => existT _ (`1 p)
                   (existT _ (k (`1 (`2 p))) (sub_image_witness k Hk p)))
       _).
  intros p q Hpq; exact Hpq.
Defined.

Lemma sub_image_monotone {u v : @SubObj Sets@{o so} A} :
  sub_le u v → sub_le (sub_image u) (sub_image v).
Proof.
  intros [k Hk].
  exists (sub_image_map k Hk).
  intro p; reflexivity.
Qed.

(* The setoid upgrade. Both comparison maps preserve the first projection, and the image setoid compares nothing else, so the two inverse laws close by [reflexivity]. / 集合论升级。两个比较映射都保持第一个投影，并且像的集合论不比较其他东西，因此两个逆律通过 [reflexivity] 收敛。 *)
#[export] Instance sub_image_respects :
  Proper (equiv ==> equiv) sub_image.
Proof.
  intros u v [i Hi].
  assert (Hfrom : sub_mono u ∘ from i ≈ sub_mono v).
  { rewrite <- Hi, <- comp_assoc, iso_to_from; cat. }
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := sub_image_map (to i) Hi
                     ; from := sub_image_map (from i) Hfrom |}.
    + intro p; simpl; reflexivity.
    + intro p; simpl; reflexivity.
  - intro p; simpl; reflexivity.
Qed.

End SubImage.

Arguments sub_image {A B} f u.
Arguments sub_image_monotone {A B} f {u v} H.

(* ------------------------------------------------------------------------ *)
(* * ** (C) The transposition, at subobject level / * ** (C) 在子对象级别的置换 *)

Section SubTranspose.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* Left to right. The image's epi leg supplies the second pullback leg and Instance/Sets/Image.v's [Sets_Image_comm] the square. / 从左到右。图像的上翘腿提供第二个回撤腿，Instance/Sets/Image.v 的 [Sets_Image_comm] 方块。 *)
Lemma sub_image_transpose_to (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le (sub_image f u) v → sub_le u (sub_reindex f v).
Proof.
  intros [k Hk].
  assert (Hsq : f ∘ sub_mono u
                  ≈ sub_mono v ∘ (k ∘ Sets_Image_epi (f ∘ sub_mono u))).
  { rewrite comp_assoc, Hk.
    intro p; reflexivity. }
  destruct (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
              (sub_dom u) (sub_mono u)
              (k ∘ Sets_Image_epi (f ∘ sub_mono u)) Hsq)
    as [w [Hw1 Hw2] _].
  exact (existT _ w Hw1).
Defined.

(*
 Right to left.  The map sends an image point to the second pullback
 projection of the mediator.  The membership equation is factored out
 first, because it serves twice: as the map's own respectfulness proof
 (through monicity) and as the [sub_le] witness. 

 --------
 从右到左。该映射将图像点发送到中介的第二回拉投影。首先将会员方程分解出来，因为它有两种用途：作为映射自身的尊重性证明（通过单射性）以及作为 [sub_le] 见证。
*)
Lemma sub_transpose_from_eq (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B)
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom (sub_reindex f v))
  (Hk : sub_mono (sub_reindex f v) ∘ k ≈ sub_mono u)
  (p : carrier (Sets_Image (f ∘ sub_mono u))) :
  sub_mono v (pullback_snd f (sub_mono v) (pullback f (sub_mono v))
                (k (`1 (`2 p)))) ≈ `1 p.
Proof.
  transitivity (f (sub_mono u (`1 (`2 p)))).
  - symmetry.
    transitivity (f (pullback_fst f (sub_mono v) (pullback f (sub_mono v))
                       (k (`1 (`2 p))))).
    + symmetry; exact (proper_morphism f _ _ (Hk (`1 (`2 p)))).
    + exact (pullback_commutes f (sub_mono v) (pullback f (sub_mono v))
               (k (`1 (`2 p)))).
  - exact (`2 (`2 p)).
Qed.

(* RESPECTFULNESS IS WHERE MONICITY IS SPENT: two image points with one first projection may carry different preimages, and only injectivity of a mono in [Sets] identifies the two values. / 尊重是单一性发挥作用的地方：两个图像点在一次投影下可能对应不同的原像，只有在 [Sets] 中单态的单射性才能识别这两个值。 *)
Definition sub_transpose_from_map (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B)
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom (sub_reindex f v))
  (Hk : sub_mono (sub_reindex f v) ∘ k ≈ sub_mono u) :
  sub_dom (sub_image f u) ~{Sets@{o so}}~> sub_dom v.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _ _ _ _
       (fun p => pullback_snd f (sub_mono v) (pullback f (sub_mono v))
                   (k (`1 (`2 p)))) _).
  intros p q Hpq.
  apply (snd (injectivity_is_monic (sub_mono v)) (sub_is_monic v)).
  transitivity (`1 p); [ exact (sub_transpose_from_eq u v k Hk p) | ].
  transitivity (`1 q); [ exact Hpq | ].
  symmetry; exact (sub_transpose_from_eq u v k Hk q).
Defined.

Lemma sub_image_transpose_from (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le u (sub_reindex f v) → sub_le (sub_image f u) v.
Proof.
  intros [k Hk].
  exact (existT _ (sub_transpose_from_map u v k Hk)
           (sub_transpose_from_eq u v k Hk)).
Defined.

Definition sub_image_reindex_iffT (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le (sub_image f u) v ↔ sub_le u (sub_reindex f v) :=
  (sub_image_transpose_to u v, sub_image_transpose_from u v).

End SubTranspose.

(* ------------------------------------------------------------------------ *)
(* * ** (D) The bridges to the Prop-valued subsets of #311 / * ** (D) 通向 #311 的 Prop 值子集的桥梁 *)

Section Bridges.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* The direct image of the subobject a subset names IS that subset's direct image -- at [≈], because the two truncated existentials are bracketed differently and each direction reassociates. / 子对象子集名称的直接像是该子集的直接像——在 [≈] 处，因为两个截断的存在量词括号不同，并且每个方向都会重新结合。 *)
Lemma sub_image_is_Powerset_Prop_image
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
    ≈ Powerset_Prop_image@{o} f S.
Proof.
  intro b; split; intros Hb Q k.
  - refine (Hb Q _); intros [p Hp].
    apply k; exists (`1 (`1 (`2 p))); split.
    + exact (`2 (`1 (`2 p))).
    + transitivity (`1 p); [ exact (`2 (`2 p)) | exact Hp ].
  - refine (Hb Q _); intros [a [Ha Hfa]].
    apply k.
    unshelve refine (existT _ _ _).
    + exists b; exists (existT _ a Ha); exact Hfa.
    + reflexivity.
Qed.

(* ... and dually for the preimage. / ... 并且对于原像也是双重的。 *)
Lemma sub_reindex_is_Powerset_Prop_preimage
  (T : carrier (Powerset_Prop_obj@{o} B)) :
  Powerset_subset_of_subobject@{o so}
      (sub_reindex f (Powerset_subobject_of_subset@{o so} T))
    ≈ Powerset_Prop_preimage@{o} f T.
Proof.
  intro a; split.
  - intro Ha.
    refine (Ha (T (f a)) _); intros [p Hp].
    refine (proj1 (@proper_morphism _ _ _ _ T (`1 (snd (`1 p))) (f a) _)
              (`2 (snd (`1 p)))).
    symmetry.
    transitivity (f (fst (`1 p))).
    + exact (proper_morphism f _ _ (symmetry Hp)).
    + exact (`2 p).
  - intro Ha.
    apply Powerset_squash_intro@{o}.
    unshelve refine (existT _ _ _).
    + unshelve refine (existT _ (a, existT _ (f a) Ha) _).
      reflexivity.
    + reflexivity.
Qed.

(*
 Consequently the Type-valued subobject order maps to the Prop-valued
 subset order: a factorization between subobjects yields inclusion of
 the subsets they name. 

 --------
 因此，类型值子对象的顺序映射到命题值子集的顺序：子对象之间的分解会产生它们所命名的子集的包含关系。
*)
Lemma subset_le_of_sub_le (u v : @SubObj Sets@{o so} A) :
  sub_le u v →
  ∀ a, Powerset_subset_of_subobject@{o so} u a
       → Powerset_subset_of_subobject@{o so} v a.
Proof.
  intros [k Hk] a Ha Q j.
  refine (Ha Q _); intros [p Hp].
  apply j; exists (k p).
  transitivity (sub_mono u p); [ exact (Hk p) | exact Hp ].
Qed.

End Bridges.
