Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(* * * Colimits of the Type-valued [Top]: what is formable, and the walls / * * 类型值 [Top] 的余极限：可形成的内容，以及壁 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.9, book p. 134 (PDF p. 143), "Similar constructions yield
 coproducts (= disjoint unions) and general colimits in Top"
 (maclane:V.9:remark2), as in Instance/Top/Cocomplete.v's header
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/quotient+space

 BACKGROUND.  Instance/Top/Cocomplete.v proves Mac Lane's Remark 2 over
 the Prop-valued [PTopCat], by the maintainer's decision of 2026-09-24
 on #458.  This file records what the tree's Type-valued [Top@{h o}]
 (Instance/Top.v) supports, whose homs sit strictly above its points
 ([o < h]) and whose opens are Type-valued predicates at [o].  Two
 constructions are formable and are built; three steps of the route
 to cocompleteness are refused, and the refusals are recorded below;
 above the points cocompleteness is refuted under informative excluded
 middle, or under decidable equality of spaces
 (Instance/Top/Cocomplete/Refutations.v's [Top_not_cocomplete_IEM] and
 [Top_not_cocomplete_ObjDecEq], Freyd's argument through an arrow index
 moved between hom universes, and [Top_not_cocomplete_Cantor_IEM] and
 [Top_not_cocomplete_Cantor_ObjDecEq], Cantor's, the last needing
 [Set < o]).  At shapes at or below the points it is left open.

 WHAT IS HERE.
 - [TSigma Ix X], the disjoint union of a family of spaces indexed by
 a type at or below the points' universe, with the final topology
 for its injections: [tsig_open] asks that a Type-valued predicate
 respect the points' equality and that its restriction to every
 summand be open ([TSigma_open], at [eq_refl]).  [tsig_inj],
 [tsig_case], [tsig_desc], and [Top_HasIndexedCoproducts_small],
 the coproducts of [Top] at those index universes.
 - [Top_HasCoequalizers]: the coequalizer of [f g : x ~> y] is
 Instance/Top/Subspace/TypeValued.v's quotient space [TQuot] on
 Instance/Sets/Coequalizer.v's [SetsCoeq] of the underlying maps
 ([Top_coequalizer_obj], at [eq_refl]); the descended map respects
 the generated relation by [coeq_rel_of_cofork].  It is built
 DIRECTLY, not by the dual of Proposition 1: over [Top] the
 quotient construction is not an adjunction record (Instance/Top/
 Subspace/TypeValued.v's header quotes the refusal, "Cannot enforce
 h = o").  So it is NOT a witness of Remark 2's sentence "this dual
 proposition and the above adjunction prove that Top has
 coequalizers"; that witness is Instance/Top/Subspace.v's
 [PTop_HasCoequalizers], over [PTopCat].

 THE WALLS, measured in a scratch file carrying the six files of #458
 after the union of their import lists (Structure/Limit/FromProducts.v
 and Structure/Complete.v among them), each refusal read in a full copy
 of that file with its one guarded command unguarded; a universe the
 message generates is written <1>, <2>, <3>.
 W1, the book's route.  [Cocomplete_from_coproducts_coequalizers]
 fed [Top_HasIndexedCoproducts_small] and [Top_HasCoequalizers] is
 refused, with the universes annotated [@{o h +| o < h +}] and with
 all of them left to inference alike: "universe inconsistency:
 Cannot enforce <1> = <2> because <1> <= <3> < <2>", where, read
 against the two types the message prints, <1> is the coproducts'
 index universe, <3> the points' and <2> the homs'.  The theorem's
 own type asks for [HasIndexedCoproducts@{u u0 u0 u2 u0}],
 coproducts indexed at the hom universe, and [TSigma]'s index sits
 at or below the points', since the sigma of the family must be a
 setoid there.  Read at an index universe [h],
 [Top_HasIndexedCoproducts_small] is refused the same way ("Cannot
 enforce <1> = h because <1> <= o < h").  Control: both ingredients
 are accepted on their own.
 W2, the direct route's relation.  Instance/Sets/Cocomplete.v's
 [colim_rel], restated for a diagram [F : D ⟶ Top@{h o}] with
 [D : Category@{s h h}] and [s <= o] as a Type-valued relation at
 [Type@{o}], is refused: "Universe inconsistency.  Cannot enforce
 h <= o because o < h".  Its glue constructor quantifies over the
 arrows of [D], which sit at [h].  Control: the same inductive at
 [Type@{h}] is accepted, and reading it as a relation at [Type@{o}]
 is refused with the same message.
 W3, a Prop-valued relation.  The same relation valued in [Prop]
 fits at [Type@{o}] (control), and the mediator into a competing
 apex respects it up to [inhabited] (control, proved by induction
 on the relation).  Eliminating it into the Type-valued [≈] of the
 apex is refused: "Incorrect elimination of "H" in the inductive
 type "tcolim_prel": the return type has sort "Type" while it
 should be SProp or Prop", and so is unwrapping the squash,
 "Incorrect elimination of "w" in the inductive type "inhabited"".
 The points of a [TopSpace] form a [SetoidObject@{o o}] with
 Type-valued [≈], and a colimit apex needs the relation itself, not
 its truth.
 Test/ProbeTopComplete458.v pins this.

 STRENGTHS.  At [eq_refl]: [TSigma_carrier], [TSigma_open] and
 [Top_coequalizer_obj].  Up to [≈]: the universal properties
 [tsig_desc] and [tcoeq_desc].  Two [Defined] ([tsig_desc],
 [tcoeq_desc]), counted by token; neither is load-bearing here (each
 closed [Qed] alone in a scratch copy of this file, which then
 compiled), and they stay transparent so that the mediators compute.

 UNIVERSES, read by [About] under [Set Printing Universes].
 - [TSigma@{o i}]: [i <= o] and stdlib caps.
 [Top_HasIndexedCoproducts_small@{o h u u0 u1} :
 HasIndexedCoproducts@{u u0 h h h} Top@{h o}]: the index universe
 [u0] with [u0 <= o], the class's own [u0 < u], and [o < u1], the
 object universe of the [Sets] in which Instance/Sets/Products.v's
 [Sets_icoprod_inj] (which [tsig_inj] consumes) types its arrow.
 - [Top_HasCoequalizers@{o h} : HasCoequalizers@{h h} Top@{h o}]:
 [o < h] and stdlib caps only.
 - No block of this file's 23 constants (its [Print Module] listing;
 it declares no obligation, record or inductive) mentions [Set],
 and none carries an equation.

 NOT DELIVERED.  Cocompleteness of [Top] at any shape universe: at or
 below the points it is open, the three walls above blocking the two
 routes tried; coproducts indexed at the hom universe (W1); the dual
 of Proposition 1 over [Top]; and any comparison of [TSigma] or of
 [Top_HasCoequalizers] with Instance/Top/Coproduct.v's binary
 [Sum_Top] or Instance/Top/Pushout.v's pushouts. 

 --------
 Mac Lane，《为工作中的数学家而设的范畴论》，第2版（GTM 5），§V.9，第134页（PDF第143页），“类似的构造产生了Top中的余积（=不交并）和一般余极限”（maclane:V.9:remark2），如Instance/Top/Cocomplete.v的标题所示 nLab: https://ncatlab.org/nlab/show/Top nLab: https://ncatlab.org/nlab/show/quotient+space背景。Instance/Top/Cocomplete.v 在由维护者于 2026-09-24 对 #458 的决定中，证明了 Mac Lane 关于 Prop 值 [PTopCat] 的注释 2。该文件记录了树的 Type 值 [Top@{h o}]（Instance/Top.v）所支持的内容，其同态严格位于其点之上（[o < h]），其开集是在 [o] 上的 Type 值谓词。可以构造两种构造，并已建立；到余完备性的三步路线被拒绝，拒绝记录如下；在点之上，在信息排中律下或在空间的可判等性下，余完备性被驳斥（Instance/Top/Cocomplete/Refutations.v 的 [Top_not_cocomplete_IEM] 和 [Top_not_cocomplete_ObjDecEq]，Freyd 通过在同态宇宙之间移动箭头索引的论证，以及 [Top_not_cocomplete_Cantor_IEM] 和 [Top_not_cocomplete_Cantor_ObjDecEq]，Cantor 的证明，最后需要 [Set < o]）。在该点或以下的形状保持开放。这里的内容是什么。-  [TSigma Ix X]，按一个类型在或低于点的类型的索引的空间族的不相交并集，其注入映射的最终拓扑：[tsig_open] 要求一个值为类型的谓词尊重点的等式，并且其对每个加和子集的限制都是开集（[TSigma_open]，在 [eq_refl]）。[tsig_inj]，[tsig_case]，[tsig_desc] 和 [Top_HasIndexedCoproducts_small]，是那类索引类型中的 [Top] 的上积。-  [Top_HasCoequalizers]：[f g : x ~> y] 的等化器是 Instance/Top/Subspace/TypeValued.v 的商空间 [TQuot]，在 Instance/Sets/Coequalizer.v 的基映射 [SetsCoeq] 上（[Top_coequalizer_obj]，在 [eq_refl]）；下降映射尊重由 [coeq_rel_of_cofork] 生成的关系。它是直接构建的，而不是通过命题 1 的对偶：在  [Top] 上，商构造不是一个伴随记录（Instance/Top/Subspace/TypeValued.v 的标题中引用了拒绝，"无法强制 h = o"）。所以它不是备注 2 中句子“这个对偶命题和上述伴随证明了 Top 有余等化子”的见证；那个见证是 Instance/Top/Subspace.v 的 [PTop_HasCoequalizers] ，在 [PTopCat] 上。墙壁，在一个包含#458的六个文件的草稿文件中测量，在合并它们的导入列表（其中包括Structure/Limit/FromProducts.v和Structure/Complete.v）之后，每次拒绝操作都会在未保护其单个受保护命令的情况下读取该文件的完整副本；消息生成的宇宙被写为<1>、<2>、<3>。W1，是书中的路径。[Cocomplete_from_coproducts_coequalizers] 输入到 [Top_HasIndexedCoproducts_small] 和 [Top_HasCoequalizers] 被拒绝，宇宙标注为 [@{o h +| o < h +}]，并且所有宇宙都保持推断状态一致：“宇宙不一致：无法强制 <1> = <2> 因为 <1> <= <3> < <2>”，其中，根据消息打印的两种类型读取，<1> 是余积的索引宇宙，<3> 是点的宇宙，<2> 是Homs的宇宙。定理自身的类型要求 [HasIndexedCoproducts@{u u0 u0 u2 u0}]，在同宇宙下索引的余积，而 [TSigma] 的索引位于或低于点处，因为族的 sigma 必须在那里是一个集合等价类。在索引宇宙 [h] 下读取，[Top_HasIndexedCoproducts_small] 以相同方式被拒绝（"无法强制 <1> = h 因为 <1> <= o < h"）。控制：两个成分单独存在时都被接受。W2，直接路径的关系。Instance/Sets/Cocomplete.v 的 [colim_rel]，重新陈述为图表 [F : D ⟶ Top@{h o}]，其中 [D : Category@{s h h}] 和 [s <= o] 作为在 [Type@{o}] 上的类型值关系，被拒绝：“宇宙不一致。无法强制 h <= o 因为 o < h”。它的粘合构造函数量化 [D] 的箭头，这些箭头位于 [h]。控制：在 [Type@{h}] 处接受相同的归纳，并且在 [Type@{o}] 处将其读取为关系时以相同的消息被拒绝。W3，一个 Prop 值的关系。在 [Prop] 中取值的相同关系适合在 [Type@{o}]（控制）处使用，并且进入竞争顶点的中介者在 [inhabited] 处尊重它（通过对关系进行归纳证明控制）。将其消除为顶点的 Type 值 [≈] 被拒绝：“在归纳类型 'tcolim_prel' 中不正确地消除了 'H'：返回类型的 sort 为 'Type'，而它应该是 SProp 或 Prop”，展开 squash 也同样会被拒绝，“在归纳类型 'inhabited' 中不正确地消除了 'w'”。[TopSpace] 的点形成一个 [SetoidObject@{o o}]，具有类型值 [≈]，并且余极点需要关系本身，而不是它的真值。Test/ProbeTopComplete458.v 确认了这一点。

 优点。在 [eq_refl]：[TSigma_carrier]、[TSigma_open] 和 [Top_coequalizer_obj]。直到 [≈]：普遍性 [tsig_desc] 和 [tcoeq_desc]。两个 [Defined]（[tsig_desc]，[tcoeq_desc]），按标记计数；这里没有承重作用（每个 [Qed] 单独放在此文件的副本中，然后编译），它们保持透明，以便中介者进行计算。宇宙，由 [About] 在 [Set Printing Universes] 下读取。
 - [TSigma@{o i}]：[i <= o] 和标准库大写字母。
 [Top_HasIndexedCoproducts_small@{o h u u0 u1}：
 HasIndexedCoproducts@{u u0 h h h} Top@{h o}]：索引宇宙
 [u0] 与 [u0 <= o]，类自身的 [u0 < u]，以及 [o < u1]，
 对象宇宙为 [Sets]，其中 Instance/Sets/Products.v 的
 [Sets_icoprod_inj]（被 [tsig_inj] 消耗）对其箭头进行类型定义。
 - [Top_HasCoequalizers@{o h} : HasCoequalizers@{h h} Top@{h o}]：
 仅 [o < h] 和标准库大写字母。
 - 本文件的 23 个常量块（其 [Print Module] 列表；
 它未声明任何义务、记录或归纳类型）均未提及 [Set]，
 且均不包含等式。未交付。[Top] 在任意形态宇宙下的共完备性：在或低于该点的地方它是开放的，三个墙壁在上方阻挡了尝试的两条路径；在同类宇宙 (W1) 中索引的余积；[Top] 上命题 1 的对偶；以及 [TSigma] 或 [Top_HasCoequalizers] 与 Instance/Top/Coproduct.v 的二元 [Sum_Top] 或 Instance/Top/Pushout.v 的推广之间的任何比较。
*)

#[local] Obligation Tactic := idtac.

(* * ** Coproducts at an index universe at or below the points / * ** 指数宇宙中或位于点以下的余积 *)

Section TSigma.

Universes o i.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → TopSpace@{o}).

Definition tsig_setoid : SetoidObject@{o o} :=
  Sets_icoprod_obj (fun k => top_carrier (X k)).

(* The final topology for the injections, Type-valued: a predicate is open when it respects the points' equality and every restriction to a summand is open. / 注射的最终拓扑，类型值：当谓词尊重点的相等性并且对每个加法子集的限制都是开放的时，该谓词是开放的。 *)
Definition tsig_open (W : tsig_setoid → Type@{o}) : Type@{o} :=
  ((∀ p q : tsig_setoid, p ≈ q → W p → W q) ∧
   (∀ k : Ix, IsOpen (X k) (fun x => W (existT _ k x))))%type.

Lemma tsig_open_respects (U V : tsig_setoid → Type@{o}) :
  (∀ p, U p ↔ V p) → tsig_open U → tsig_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros p q e v. apply (fst (H q)), (Hp p q e), (snd (H p)), v.
  - intro k.
    exact (open_respects (X k) _ _ (fun x => H (existT _ k x)) (Ho k)).
Qed.

Lemma tsig_open_proper (U : tsig_setoid → Type@{o}) :
  tsig_open U → ∀ p q : tsig_setoid, p ≈ q → U p → U q.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma tsig_open_union (I : Type@{o}) (U : I → tsig_setoid → Type@{o}) :
  (∀ j, tsig_open (U j)) → tsig_open (fun p => { j : I & U j p }).
Proof.
  intro HU; split.
  - intros p q e [j u]; exact (j; fst (HU j) p q e u).
  - intro k. exact (open_union (X k) I (fun j x => U j (existT _ k x))
                      (fun j => snd (HU j) k)).
Qed.

Lemma tsig_open_whole : tsig_open (fun _ => poly_unit@{o}).
Proof. split; [intros; exact ttt|intro k; exact (open_whole (X k))]. Qed.

Lemma tsig_open_inter (U V : tsig_setoid → Type@{o}) :
  tsig_open U → tsig_open V → tsig_open (fun p => U p ∧ V p).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros p q e [u v]; exact (HpU p q e u, HpV p q e v).
  - intro k; exact (open_inter (X k) _ _ (HoU k) (HoV k)).
Qed.

Definition TSigma : TopSpace@{o} := {|
  top_carrier   := tsig_setoid;
  IsOpen        := tsig_open;
  open_respects := tsig_open_respects;
  open_proper   := tsig_open_proper;
  open_union    := tsig_open_union;
  open_whole    := tsig_open_whole;
  open_inter    := tsig_open_inter
|}.

Example TSigma_carrier : top_carrier TSigma = tsig_setoid := eq_refl.

Example TSigma_open (W : tsig_setoid → Type@{o}) :
  IsOpen TSigma W = tsig_open W := eq_refl.

End TSigma.

Section TSigmaUMP.

Universes o h i.
Constraint o < h.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → Top@{h o}).

Definition tsig_inj (k : Ix) : X k ~{Top@{h o}}~> TSigma Ix X :=
  Build_ContinuousMorphism (X k) (TSigma Ix X)
    (Sets_icoprod_inj (fun k => top_carrier (X k)) k)
    (fun W HW => snd HW k).

Lemma tsig_case_cont (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  Continuous (TSigma Ix X) Z
    (Sets_icoprod_case (fun k => top_carrier (X k)) (top_carrier Z)
       (fun k => continuous_map (iota k))).
Proof.
  intros W HW; split.
  - intros p q e w.
    exact (open_proper Z W HW _ _
             (proper_morphism (Sets_icoprod_case (fun k => top_carrier (X k))
                (top_carrier Z) (fun k => continuous_map (iota k))) p q e) w).
  - intro k. exact (continuity (iota k) W HW).
Qed.

Definition tsig_case (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  TSigma Ix X ~{Top@{h o}}~> Z :=
  Build_ContinuousMorphism _ _ _ (tsig_case_cont Z iota).

Definition tsig_desc (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  ∃! u : TSigma Ix X ~{Top@{h o}}~> Z, ∀ k, u ∘ tsig_inj k ≈ iota k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tsig_case Z iota).
  - intros k x; reflexivity.
  - intros v Hv [k x]; simpl. symmetry. exact (Hv k x).
Defined.

End TSigmaUMP.

(* Indexed coproducts of the Type-valued [Top], at index types at or below the points' universe. / 在类型值 [Top] 的索引积中，索引类型在或低于点的宇宙。 *)
Definition Top_HasIndexedCoproducts_small@{o h +| o < h +} :
  HasIndexedCoproducts Top@{h o} :=
  @Build_HasIndexedCoproducts Top@{h o}
    (fun A f => TSigma A f)
    (fun A f k => tsig_inj A f k)
    (fun A f => Build_IsIndexedCoproduct f _ _
                  (fun c iota => tsig_desc A f c iota)).

(* * ** Coequalizers: the quotient topology on the [Sets] coequalizer / * ** 等化子：在 [Sets] 等化子上的商拓扑 *)

Section TCoeq.

Universes o h.
Constraint o < h.

Context {x y : Top@{h o}} (f g : x ~{Top@{h o}}~> y).

Definition tcoeq_obj : TopSpace@{o} :=
  TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
    (sets_coeq_proj (continuous_map f) (continuous_map g)).

Definition tcoeq_proj : y ~{Top@{h o}}~> tcoeq_obj := tquot_proj y _ _.

Lemma tcoeq_cofork : tcoeq_proj ∘ f ≈ tcoeq_proj ∘ g.
Proof. intro a; simpl. exact (cq_glue _ _ a). Qed.

(*
 The descended map on points: a coforking map respects the relation the
 pair generates (Instance/Sets/Coequalizer.v's [coeq_rel_of_cofork]). 

 --------
 在点上的下降映射：共分叉映射遵守该对生成的关系（Instance/Sets/Coequalizer.v 的 [coeq_rel_of_cofork]）。
*)
Definition tcoeq_med {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : k ∘ f ≈ k ∘ g) :
  SetoidMorphism@{o o o} (SetsCoeq (continuous_map f) (continuous_map g))
    (top_carrier z) :=
  @Build_SetoidMorphism _
    (is_setoid (SetsCoeq (continuous_map f) (continuous_map g))) _
    (is_setoid (top_carrier z))
    (continuous_map k)
    (fun b1 b2 H =>
       coeq_rel_of_cofork (continuous_map f) (continuous_map g)
         (continuous_map k) Hk b1 b2 H).

Definition tcoeq_desc {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : k ∘ f ≈ k ∘ g) :
  ∃! u : tcoeq_obj ~{Top@{h o}}~> z, u ∘ tcoeq_proj ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tquot_desc y (SetsCoeq (continuous_map f) (continuous_map g))
      (sets_coeq_proj (continuous_map f) (continuous_map g)) z k
      (tcoeq_med k Hk) (fun b => reflexivity _)).
  - intro b; reflexivity.
  - intros v Hv b. simpl. symmetry. exact (Hv b).
Defined.

Definition tcoeq_IsCoequalizer :
  IsCoequalizer f g tcoeq_obj tcoeq_proj :=
  @Build_IsCoequalizer Top@{h o} x y f g tcoeq_obj tcoeq_proj tcoeq_cofork
    (fun z k Hk => tcoeq_desc k Hk).

End TCoeq.

Definition Top_HasCoequalizers@{o h +| o < h +} : HasCoequalizers Top@{h o} :=
  @Build_HasCoequalizers Top@{h o}
    (fun x y f g =>
       (tcoeq_obj f g; (tcoeq_proj f g; tcoeq_IsCoequalizer f g))).

(* The coequalizer IS the quotient topology on the [Sets] coequalizer of the underlying maps, on the nose. / 等化子就是在基础映射的 [Sets] 等化子上的商拓扑，本质上就是如此。 *)
Example Top_coequalizer_obj@{o h +| o < h +} {x y : Top@{h o}}
  (f g : x ~{Top@{h o}}~> y) :
  `1 (@coeq _ Top_HasCoequalizers x y f g)
    = TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
        (sets_coeq_proj (continuous_map f) (continuous_map g)) := eq_refl.
