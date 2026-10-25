Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(* * * The category of adjunctions between two fixed categories / * * 两个固定范畴之间的伴随范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors
 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7
 "Transformations of Adjoints", book p. 101: display (8) and the
 paragraph that names the category.

 Mac Lane's own sentence, from that page: "For the two given categories
 X and A we thus have a new category A^(adj)X, the CATEGORY OF ADJUNCTIONS
 from X to A; its objects are the adjunctions <F, G; eta, eps>; its arrows
 are the transformations (conjugate pairs) <sigma, tau>, with the
 composition just noted."

 LETTERS.  Mac Lane's adjunction <F, G, phi, eta, eps> : X ⇀ A has
 F : X ⟶ A on the left and G : A ⟶ X on the right, so his X is this
 file's D and his A is this file's C, matching the library's own
 orientation F : D ⟶ C, U : C ⟶ D.  His G is this file's U.

 objects        triples (F, U, F ⊣ U), the type [AdjObj]
 arrows         conjugate pairs, the record [ConjPair]
 identity       the pair (nat_id, nat_id)
 composition    display (8), see below

 This is the hom-category between C and D of the 2-category Adj of
 categories, adjunctions, and their maps; the sibling file
 [Instance.Adjoints] instead bundles categories and adjunctions into a
 1-category (objects are categories, arrows are adjunctions).

 THE CONDITION ON AN ARROW, WHICH THIS FILE NOW IMPOSES.  A morphism of
 this category is not a bare pair of natural transformations: sigma and
 tau are required to be CONJUGATE, that is, to correspond under the two
 hom-set transposes.  That condition is [Conjugate] of
 Adjunction/Conjugate.v, which is Mac Lane's §IV.7 Definition 2 hom-set
 square quantified over every transposable arrow; [conjugate_iff_from]
 there reads the same square through the inverse transposes and
 [conjugate_characterizations] proves the four equivalent pasting forms
 (the two mate formulas and the unit and counit equations).  The record
 [ConjPair] below carries that square as its third field, so the hom is
 the product of the two transformation setoids CUT DOWN by that square,
 and the pair (nat_id, nat_id) and the composite pair have to be PROVED
 to satisfy it.  (That the cut is STRICT is not proved here: no pair of
 transformations that is not conjugate is exhibited.)  This supersedes
 the caveat this file used to carry, which recorded that its hom was the
 bare product setoid ([D,C] × [C,D]) with no such condition, that every
 category obligation therefore discharged with no content, and that
 retyping the hom was future work.  The old
 coarse category is NOT kept: nothing in the tree consumed it, measured
 by USE rather than by name -- before this change no `.v` file anywhere
 Required Category.Instance.Adj (the sibling Instance/Adj/Forgetful.v,
 added alongside, is the first), and every other occurrence of the bare
 token [Adj] in the tree is a local hypothesis of that name or is prose
 (four of them section variables, hence glob-recorded as `var` rather
 than as declarations; the rest are [intros]-bound or prose).
 Adjunction/Map.v's RELATION paragraph described the OLD hom of this
 file; it is corrected in the same commit rather than left stale.

 THE VARIANCE, WHICH IS THE ONE DESIGN DECISION.  Conjugate.v declares

 Conjugate (A : F ⊣ U) (A' : F' ⊣ U') (sigma : F' ⟹ F) (tau : U ⟹ U')

 -- sigma BACKWARD and tau FORWARD relative to the primes.  Mac Lane's
 p. 101 labels the pair the other way: in his forgetful-functor display
 sigma points DOWN, from F to F', and tau points UP, from G' to G, so a
 transformation from the first adjunction to the second is
 sigma : F ⟹ F' together with tau : G' ⟹ G.  That labelling is the same
 relation with its two adjunction arguments EXCHANGED, not a second
 notion, exactly as Conjugate.v's own ORIENTATION note records for
 Riehl.  So the hom from x to y here is

 Conjugate (adjobj_adj y) (adjobj_adj x) sigma tau

 which types sigma : (left of x) ⟹ (left of y) and
 tau : (right of y) ⟹ (right of x).  The positive half of that is pinned
 by [ConjPair]'s own field types below, which typecheck only under this
 reading; the negative half -- that [Conjugate A' A] REJECTS
 sigma : F' ⟹ F at an abstract pair A : F ⊣ U, A' : F' ⊣ U' -- was
 measured out of tree; this file carries no probe, and the fact is
 pinned in Test/ProbeAdjCat395.v, added in the same commit.

 DISPLAY (8), AND WHERE THE CATEGORY LAWS NOW REST.  Mac Lane writes the
 vertical composite of two conjugate pairs as
 <sigma', tau'> ∘ <sigma, tau> = <sigma' · sigma, tau · tau'>: the SECOND
 component composes in the OPPOSITE order.  Read the label precisely: on
 the page (8) sits on the two-arrow CHAIN, and this equation is the
 unnumbered running text just below it; "display (8)" below is shorthand
 for the equation.  Both of the two proof
 obligations that the category's [id] and [compose] fields now generate
 are discharged by naming a theorem that was ALREADY IN TREE before this
 file was retyped, and neither is re-proved here:

 Adjunction/Conjugate.v  conjugate_id
 : Conjugate A1 A1 nat_id nat_id
 Adjunction/Conjugate.v  conjugate_compose
 : Conjugate A1 A2 sigma tau → Conjugate A2 A3 sigma' tau'
 → Conjugate A1 A3 (sigma ∙ sigma') (tau' ∙ tau)

 Note [(tau' ∙ tau)] in that conclusion: the donor already composes the
 second component backward, which IS display (8), and it already fits
 this category's composition with no rearrangement, since the hom from
 x to y is [Conjugate (adj y) (adj x)] and so the three adjunction
 arguments A1, A2, A3 are the codomain, the middle and the domain in
 that order.  [conj_mate_id] and [conj_mate_compose] sit beside them
 there.

 That those two obligations no longer discharge by themselves is
 MEASURED, not assumed: with four automation attempts inserted ahead of
 each [exact], neither obligation is closed by [cat], by
 [program_simpl], by [simpl; intros; cat] or by [auto], while the
 [exact] itself does close them -- eight rejections against one control,
 checked out of tree, this file carrying no probe of its own.  The
 OTHER five obligations (respectfulness of composition and the four
 category laws) are still componentwise equations between natural
 transformations and still close by the ordinary automation, just as
 they did before the retyping; what changed is that [id] and [compose]
 no longer TYPECHECK at all without the two theorems above.

 COST.  Requiring Adjunction/Conjugate.v grows this file's transitive
 in-project closure from 18 modules to 19, excluding the file itself,
 and the single added module is Adjunction/Conjugate.vo -- everything
 Conjugate.v needs, Instance/Sets included, was already reachable
 through Theory/Adjunction.v.

 THE HOM-SETOID.  Two conjugate pairs are identified when both
 components agree in the transformation setoid.  Comparing only ONE
 component would give the same relation, and that is proved rather than
 asserted: [conj_pair_right_unique] recovers agreement of the tau's from
 agreement of the sigma's, and [conj_pair_left_unique] the converse,
 each in three lines over Conjugate.v's [conj_mate_uniq] /
 [conj_mate_inv_uniq] and the matching respectfulness lemma.  This is
 the reason the third field of [ConjPair] costs nothing at the setoid
 level: a conjugate pair is determined by either of its legs.

 STRENGTHS, MEASURED STRICT FIRST.  Four [Example]s below close by
 [eq_refl] rather than by `≈`, and these are Leibniz equalities of the
 underlying [Transform] values, which is stronger than the hom-setoid's
 own `≈`: the identity's two components ARE [nat_id] on the nose
 ([adj_id_sigma], [adj_id_tau]), and the composite's two components ARE
 the two vertical composites of display (8), in the two opposite orders
 ([adj_compose_sigma], [adj_compose_tau]).  They reduce because
 [ConjPair] has primitive projections, so a projection of a record
 literal reduces whatever the opacity of the third field.

 THE 2-CATEGORICAL STRUCTURE IS NOT HERE, BUT IT EXISTS.  Mac Lane's
 §IV.8 Theorem 2 and Exercise 1 -- horizontal composition of conjugate
 pairs, its bifunctoriality, and the interchange law -- are
 Instance/Adj/Bicategory.v, which assembles [Adj_Bicategory] with the
 categories [Adj C D] built here as its hom-categories (its
 [Adj_bicat_is_Adj] records that at [eq_refl]).  Nothing in THIS file
 consumes or mentions that structure; the sentence this paragraph used
 to carry, that no 2-categorical structure existed at all, is no longer
 true of the tree and has been replaced.

 NOT DELIVERED HERE: no comparison with Theory/Bicategory/Mates.v or
 with Instance/Cat/Bicategory/Conjugate.v; no relation to
 Adjunction/Map.v's maps of adjunctions, whose
 identity-bounding-functor case is this file's hom (that file's
 [map_adj_hom_is_conjugate] records the identification, and nothing here
 consumes it); nothing about limits or colimits of [Adj C D]; and no
 concrete witness at a named pair of categories.  The two forgetful
 functors of the same page are Instance/Adj/Forgetful.v. 

 --------
 nLab：https://ncatlab.org/nlab/show/2-category+of+adjunctions
 维基百科：https://en.wikipedia.org/wiki/Adjoint_functors
 Mac Lane，《为工作中的数学家而设的范畴》，第二版，第IV.7节
 “伴随的变换”，书中第101页：公式(8)及提到该范畴的段落。

 Mac Lane在该页上的原句：“对于两个给定的范畴 X 和 A，我们因此得到一个新的范畴 A^(adj)X，即从 X 到 A 的伴随范畴；它的对象是伴随 <F, G; eta, eps>；它的箭头是变换（共轭对）<sigma, tau>，其复合如上所述。”

 字母表示。Mac Lane 的伴随 <F, G, phi, eta, eps> : X ⇀ A 的左边是 F : X ⟶ A，右边是 G : A ⟶ X，因此他的 X 是此文件的 D，他的 A 是此文件的 C，与库自身的方向 F : D ⟶ C, U : C ⟶ D 相匹配。他的 G 是此文件的 U。对象        三元组 (F, U, F ⊣ U)，类型  [AdjObj]
 箭头        共轭对，记录  [ConjPair]
 同一性       对 (nat_id, nat_id)
 组合        显示 (8)，见下文

 这是 2-范畴 Adj（由范畴、伴随以及它们的映射组成）的 C 与 D 之间的同态范畴；兄弟文件  [Instance.Adjoints]  则将范畴和伴随捆绑成一个 1-范畴（对象是范畴，箭头是伴随）。该文件现在强加在箭头上的条件。这个范畴的态射不是一对简单的自然变换：sigma 和 tau 需要是共轭的，即在两个 hom 集对换下对应。这个条件是 Adjunction/Conjugate.v 中的 [Conjugate]，即 Mac Lane §IV.7 定义 2 的 hom 集方形，对每个可对换箭头进行量化；[conjugate_iff_from] 在逆对换下读取相同的方形，而 [conjugate_characterizations] 证明了四种等价的粘贴形式（两种配偶公式以及单位和余单位方程）。下面的记录 [ConjPair] 将该方形作为它的第三字段，因此 hom 是通过该方形限制的两个变换集合的乘积，并且必须证明该对 (nat_id, nat_id) 和复合对满足该条件。（这里并未证明这个割是严格的：没有展示出非共轭的转换对。） 这取代了该文件以前的警告，该警告记录了它的 Hom 是最基本的乘积集合同构（[D,C] × [C,D]），没有这样的条件，因此每个范畴义务都没有实际内容，而且重新定义 Hom 是未来的工作。旧的粗略类别没有保留：在树中没有任何东西使用它，以使用量而非名称来衡量——在此更改之前，任何地方都没有 `.v` 文件需要 Category.Instance.Adj（旁边添加的同级 Instance/Adj/Forgetful.v 是第一个），并且在树中任何其他 [Adj] 的裸令牌出现都是该名称的局部假设或是散文（其中四个是段落变量，因此作为 `var` 全局记录而不是作为声明；其余的是 [intros] 绑定或散文）。Adjunction/Map.v 的 RELATION 段落描述了该文件的旧 hom；在同一次提交中进行了更正，而不是保持过时。

 方差，这是唯一的设计决策。Conjugate.v 声明

 Conjugate (A : F ⊣ U) (A' : F' ⊣ U') (sigma : F' ⟹ F) (tau : U ⟹ U')-- sigma 相对于素数是向后的，而 tau 是向前的。Mac Lane 第 101 页将这一对标注反过来：在他的遗忘函子显示中，sigma 指向下，从 F 到 F'，而 tau 指向上，从 G' 到 G，因此从第一个伴随到第二个伴随的变换是 sigma : F ⟹ F' 以及 tau : G' ⟹ G。这种标注与交换其两个伴随参数的关系相同，并不是第二种概念，正如 Conjugate.v 自身的方向注释为 Riehl 所记录的。因此这里从 x 到 y 的同态是

 Conjugate (adjobj_adj y) (adjobj_adj x) sigma tau哪种类型 sigma : (x 的左侧) ⟹ (y 的左侧) 以及 tau : (y 的右侧) ⟹ (x 的右侧)。其中正半部分由 [ConjPair] 自己的字段类型固定，这些类型仅在此方式下能够类型检查；负半部分——即 [Conjugate A' A] 拒绝 sigma : F' ⟹ F 在一个抽象对 A : F ⊣ U, A' : F' ⊣ U' 上——是从树外测量的；该文件没有携带任何探针，这一事实在 Test/ProbeAdjCat395.v 中被固定，并在同一次提交中添加。显示（8），以及类别律目前所处的位置。Mac Lane 将两个共轭对的垂直复合写作
 <sigma', tau'> ∘ <sigma, tau> = <sigma' · sigma, tau · tau'>：第二个分量的组合顺序相反。准确读取标签：在页面（8）上，它位于双箭头链上，而这个方程是在其下方未编号的正文中；下面的“显示（8）”是该方程的简写。类别的 [id] 和 [compose] 字段现在生成的两个证明义务，都通过命名一个在此文件重新录入之前已经存在于 TREE 中的定理来解决，并且在这里都没有重新证明。Adjunction/Conjugate.v  conjugate_id
 : Conjugate A1 A1 nat_id nat_id
 Adjunction/Conjugate.v  conjugate_compose
 : Conjugate A1 A2 sigma tau → Conjugate A2 A3 sigma' tau'
 → Conjugate A1 A3 (sigma ∙ sigma') (tau' ∙ tau)

 注意 [(tau' ∙ tau)] 在该结论中：供体已经按反向组合了第二个分量，这就是显示器 (8)，并且它已经适合该范畴的组合，无需重新排列，因为从 x 到 y 的同态是 [Conjugate (adj y) (adj x)]，因此三个伴随的参数 A1, A2, A3 按顺序为余域、中间体和定义域。[conj_mate_id] 和 [conj_mate_compose] 就在它们旁边。这两个义务不再自动解除是通过测量得出的，而非假设：在每个 [exact] 前插入四次自动化尝试后，无论是 [cat]、[program_simpl]、[simpl; intros; cat] 还是 [auto] 都无法关闭任何一个义务，而 [exact] 本身却可以关闭它们——八次拒绝对一次控制，已从树中检出，该文件本身不携带任何探针。其他五个义务（作品的尊重性以及四个类别律）仍然是自然变换之间的逐组件方程，并且仍然可以通过普通自动化来关闭，就像重打类型之前一样；改变的是 [id] 和 [compose] 在没有上述两个定理的情况下再也无法类型检查。成本。要求 Adjunction/Conjugate.v 会将该文件的及物项目内闭包从 18 个模块增加到 19 个（不包括文件本身），而唯一添加的模块是 Adjunction/Conjugate.vo —— Conjugate.v 需要的一切，包括 Instance/Sets，已经可以通过 Theory/Adjunction.v 达到。同态-集合体。当两个组成部分在变换集合体中一致时，即可识别出一对共轭对。仅比较一个组成部分也会得到相同的关系，并且这是经过证明而非断言的：[conj_pair_right_unique] 通过 sigma 的一致性恢复 tau 的一致性，而 [conj_pair_left_unique] 则是逆向操作，这些都在 Conjugate.v 的三行代码中实现：[conj_mate_uniq] / [conj_mate_inv_uniq] 以及相应的尊重性引理。这就是为什么 [ConjPair] 的第三个字段在集合体层面上不花费任何代价的原因：共轭对由任一腿就能确定。优势，严格首先衡量。下面靠近的四个 [Example] 由 [eq_refl] 而不是由 `≈` 给出，并且这些是底层 [Transform] 值的莱布尼茨等式，这比同态集合自身的 `≈` 更强：身份的两个分量在本质上是 [nat_id]（[adj_id_sigma]，[adj_id_tau]），复合的两个分量是显示（8）的两个垂直复合，以相反的顺序（[adj_compose_sigma]，[adj_compose_tau]）。它们可以化简，因为 [ConjPair] 有原始投影，所以记录字面量的投影无论第三个字段的不可见性如何都可以化简。双范畴结构不在这里，但它存在。Mac Lane 的 §IV.8 定理 2 和练习 1 ——共轭对的水平组合，其双函子性，以及交换律 —— 在 Instance/Adj/Bicategory.v 中，它将 [Adj_Bicategory] 与此处建立的类别 [Adj C D] 组装为其 Hom-范畴（其 [Adj_bicat_is_Adj] 记录了在 [eq_refl] 处的情况）。本文件中没有任何内容使用或提到该结构；本段曾经承载的那句话，即根本不存在双范畴结构，现在对于该树已经不再成立，并已被替换。未在此处提供：未与 Theory/Bicategory/Mates.v 或 Instance/Cat/Bicategory/Conjugate.v 进行比较；与 Adjunction/Map.v 中关于伴随映射的部分无关，其中恒同限制函子情况对应于此文件中的 hom（该文件中的 [map_adj_hom_is_conjugate] 记录了该识别，而这里没有任何使用它的内容）；没有关于 [Adj C D] 的极限或余极限的内容；也没有在命名的范畴对上给出具体的实例。 同一页的两个遗忘函子位于 Instance/Adj/Forgetful.v。
*)

(*
 An object of the category: a left adjoint, a right adjoint, and an
 adjunction between them.  `∃` here is [sigT], so the adjunction is data
 and no choice principle is involved. 

 --------
 一个范畴的对象：一个左伴随，一个右伴随，以及它们之间的伴随。`∃` 这里是 [sigT]，所以伴随是数据，并且不涉及选择原理。
*)
Definition AdjObj (C D : Category) : Type :=
  ∃ (F : D ⟶ C) (U : C ⟶ D), F ⊣ U.

Definition adjobj_left {C D : Category} (x : AdjObj C D) : D ⟶ C := `1 x.
Definition adjobj_right {C D : Category} (x : AdjObj C D) : C ⟶ D := `1 `2 x.
Definition adjobj_adj {C D : Category} (x : AdjObj C D) :
  adjobj_left x ⊣ adjobj_right x := `2 `2 x.

(* An arrow x ⟶ y: Mac Lane's conjugate pair <sigma, tau>, with sigma forward on the left adjoints, tau backward on the right adjoints, and the hom-set square relating them. / 一个箭头 x ⟶ y：Mac Lane 的共轭对 <sigma, tau>，其中 sigma 在左伴随上是正向的，tau 在右伴随上是反向的，并且涉及它们的同集平方。 *)
Record ConjPair {C D : Category} {x y : AdjObj C D} : Type := {
  conj_left  : adjobj_left x ⟹ adjobj_left y;
  conj_right : adjobj_right y ⟹ adjobj_right x;
  conj_pair_law :
    Conjugate (adjobj_adj y) (adjobj_adj x) conj_left conj_right
}.

(*
 Two conjugate pairs agree when both components agree; by
 [conj_pair_right_unique] and [conj_pair_left_unique] below, comparing
 either component alone would give the same relation. 

 --------
 当两个分共轭对的两个组成部分都一致时，它们就一致；通过下面的 [conj_pair_right_unique] 和 [conj_pair_left_unique]，单独比较任一组成部分会得到相同的关系。
*)
#[export]
Program Instance ConjPair_Setoid {C D : Category} {x y : AdjObj C D} :
  Setoid (@ConjPair C D x y) := {|
  equiv := fun f g => (conj_left f ≈ conj_left g)
                    ∧ (conj_right f ≈ conj_right g)
|}.
Next Obligation.
  constructor.
  - intros f; split; reflexivity.
  - intros f g [Hl Hr]; split; symmetry; assumption.
  - intros f g h [Hl Hr] [Hl' Hr']; split; etransitivity; eassumption.
Qed.

Program Definition Adj (C D : Category) : Category := {|
  obj     := AdjObj C D;
  hom     := fun x y => @ConjPair C D x y;
  homset  := fun x y => @ConjPair_Setoid C D x y;
  id      := fun x => {| conj_left := nat_id; conj_right := nat_id |};
  compose := fun x y z f g =>
    {| conj_left  := conj_left f ∙ conj_left g
     ; conj_right := conj_right g ∙ conj_right f |}
|}.
(* The identity pair is conjugate: Conjugate.v's [conjugate_id]. / 恒等元对是共轭的：Conjugate.v 的 [conjugate_id]。 *)
Next Obligation. exact (conjugate_id (adjobj_adj x)). Qed.
(*
 The composite pair is conjugate: Conjugate.v's [conjugate_compose],
 whose conclusion already composes the second component backward. 

 --------
 复合对是共轭的：Conjugate.v 的 [conjugate_compose]，其结论已经将第二个分量反向组合。
*)
Next Obligation.
  exact (conjugate_compose (adjobj_adj z) (adjobj_adj y) (adjobj_adj x)
           _ _ _ _ (conj_pair_law f) (conj_pair_law g)).
Qed.
Next Obligation. proper; simpl in *; simplify; rewrites; reflexivity. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* Either leg of a conjugate pair determines the other, so the hom-setoid above could have compared just one of them. / 共轭对的任一边都决定另一边，因此上述的同态集可以只比较其中一条边。 *)
Section Determined.
Context {C D : Category} {x y : AdjObj C D}.

Lemma conj_pair_right_unique (f g : @ConjPair C D x y) :
  conj_left f ≈ conj_left g → conj_right f ≈ conj_right g.
Proof.
  intro H.
  rewrite (conj_mate_uniq _ _ _ _ (conj_pair_law f)).
  rewrite (conj_mate_uniq _ _ _ _ (conj_pair_law g)).
  now apply conj_mate_respects.
Qed.

Lemma conj_pair_left_unique (f g : @ConjPair C D x y) :
  conj_right f ≈ conj_right g → conj_left f ≈ conj_left g.
Proof.
  intro H.
  rewrite (conj_mate_inv_uniq _ _ _ _ (conj_pair_law f)).
  rewrite (conj_mate_inv_uniq _ _ _ _ (conj_pair_law g)).
  now apply conj_mate_inv_respects.
Qed.

End Determined.

(*
 The identity and Mac Lane's display (8), pinned at Leibniz equality of
 the underlying natural transformations -- strictly stronger than the
 hom-setoid's `≈`.  The second component of a composite is the vertical
 composite taken in the OPPOSITE order, which is the whole content of
 display (8). 

 --------
 恒等和 Mac Lane 的图示 (8)，固定于底层自然变换的莱布尼茨等式 —— 严格强于同态集的 `≈`。复合的第二个分量是按相反顺序取的垂直复合，这就是图示 (8) 的全部内容。
*)

Example adj_id_sigma (C D : Category) (x : Adj C D) :
  conj_left (@id (Adj C D) x) = nat_id := eq_refl.

Example adj_id_tau (C D : Category) (x : Adj C D) :
  conj_right (@id (Adj C D) x) = nat_id := eq_refl.

Example adj_compose_sigma (C D : Category) (x y z : Adj C D)
        (f : y ~> z) (g : x ~> y) :
  conj_left (f ∘ g) = conj_left f ∙ conj_left g := eq_refl.

Example adj_compose_tau (C D : Category) (x y z : Adj C D)
        (f : y ~> z) (g : x ~> y) :
  conj_right (f ∘ g) = conj_right g ∙ conj_right f := eq_refl.
