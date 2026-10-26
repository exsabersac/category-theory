Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(* * * Subspaces and quotients over the Type-valued [Top] / * * 基于类型值 [Top] 的子空间和商空间 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.9, read from the page images: the subspace and quotient
 constructions, book pp. 132-134 (PDF pp. 141-143) (catalog ids
 maclane:V.9:construction2 and maclane:V.9:construction3; the book
 numbers neither)
 nLab: https://ncatlab.org/nlab/show/subspace+topology
 nLab: https://ncatlab.org/nlab/show/quotient+space

 WHAT THIS FILE IS.  Instance/Top/Subspace.v states Mac Lane's subspace
 and quotient constructions over Instance/Top/Prop.v's Prop-valued
 spaces, where both sliced adjunctions are [Adjunction] records.  This
 file states what of them is formable over the tree's own Type-valued
 [Top] (Instance/Top.v), and where the rest stops.  Every refusal
 quoted below was read from a scratch file compiled against this tree,
 by removing the guard of one command at a time in a full copy;
 Test/ProbeSubspace457.v pins each of the six (its N13, N14, N18, N20,
 N21 and N25).

 THE QUOTIENT FITS AT THE POINTS' UNIVERSE.  [tquot_open V] only APPLIES
 [IsOpen X], to the preimage of [V] along [q], so it is valued at the
 points' universe [o], and [TQuot X T q : TopSpace@{o}] is an object of
 the same [Top@{h o}] as [X].  Its opens are the [V] with open preimage
 that respect the equality of [T], the setoid addition described in
 Instance/Top/Subspace.v's header.  [tquot_universal] is the universal
 property over ARBITRARY spaces [Z] mapping out, both directions, and
 [tquot_desc] the book's form.

 THE SUBSPACE DOES NOT.  [tsub_open V], the book's predicate verbatim
 (“V is the preimage along h of an open of X”), quantifies over the
 opens of X and is valued at [o1] with [o < o1].  At [Type@{o}] the same
 body is refused, “universe inconsistency: Cannot enforce o < o because
 o = o”; and supplying [tsub_open] as the [IsOpen] of a [TopSpace@{o}]
 is refused, “Cannot enforce o1 <= o because o < o1”.  So the subspace
 is delivered UNPACKAGED at [o1]: the five axioms of Instance/Top.v's
 record ([tsub_open_respects], [tsub_open_proper], [tsub_open_union]
 with its index at [o] as in [open_union], [tsub_open_whole],
 [tsub_open_inter]), the continuity of [h] out of it
 ([tsub_preimage_open]), continuity into it for a setoid map from a
 space ([tsub_continuous]), and the universal property over ARBITRARY
 spaces [Z] mapping in, both directions ([tsub_universal]), with the
 book's form [tsub_lift].
 A squashed, local encoding (a point of V has, merely, an open of X
 around its image whose preimage lies in V) does fit in a
 [TopSpace@{o}], in the style of Instance/Top/CompHaus.v's
 [Top_sq_product].  It is not shown to be the subspace topology, and
 is not stated here: its opens include the book's
 (Test/ProbeSubspace457.v's [p457_sq_global_to_local] proves that
 inclusion for predicates respecting the points' equality), but the
 “if” half of its universal property, which would follow were the two
 the same, is refused along both routes tried: eliminating the squash
 into the Type-valued [IsOpen Z], “Cannot enforce o <= Prop”, and
 taking a union indexed by the squashed data, “Cannot enforce o1 <= o
 because o < o1” (#457's scouting prototype of that encoding, rebuilt
 in Test/ProbeSubspace457.v, whose N20 and N21 these are).
 Instance/Top/CompHaus.v records the same trap for the product.
 The OPEN case is different: Instance/Top/Presheaf.v's [OpenSub U], the
 subspace on an open subset, is a [TopSpace] at the points' universe,
 and its universal property over arbitrary spaces mapping in holds; a
 scratch file importing Presheaf.v re-derives the “if” half from
 [sub_ext_recovers], closed under the global context.  It is not
 imported here: Presheaf.v requires the stdlib reals.

 THE SLICED FUNCTORS AND THE TRANSPOSITIONS.  [Top_Forget_over X] and
 [Top_Forget_under X] are Mac Lane's G ↓ X and X ↓ G at Instance/Top/
 Forgetful.v's [Top_Forget], into the slices of the LIFTED [Sets@{h so}]
 that [Top_Forget] lands in.  [TQuot_Functor X] is M, out of the coslice
 of the UNLIFTED [Sets@{o so}] into the coslice of [Top@{h o}].  The
 adjunction [TQuot_Functor X ⊣ Top_Forget_under X] is refused: its
 functors go from a category with homs at [o] to one with homs at [h],
 and [Adjunction] identifies the hom levels of its two categories
 (Theory/Adjunction.v, About: [h1 = h2]), “Cannot enforce h = o because
 o < h”.  What IS formable is the Forgetful.v reading: the hom-set
 bijections as cross-universe isomorphisms, the small side lifted by
 Instance/Sets/Classifier.v's [Setoid_Lift].
 - [tquot_adj x y]: maps under X out of [TQuot] against maps of the
 unlifted coslice into [tstrip_under y], the space [y] stripped to its
 points and underlying map ([Top_Forget_under X y] is its lift, at
 [eq_refl] by [tstrip_under_lift], not a functor image: a functor
 from homs at [h] to homs at [o] is the Forgetful.v refusal).  Both
 directions are the identity on underlying maps
 ([tquot_adj_to_map], [tquot_adj_from_map], at [eq_refl]);
 [tquot_adj_nat_l] and [tquot_adj_nat_r] are the two naturality
 squares [Build_Adjunction'] asks of [to], with [tstrip_under_map]
 in place of [fmap] of the forgetful functor.
 [tquot_obj_stripped] is Mac Lane's “X ↓ G after M is the identity”,
 stripped (Leibniz, [Defined]; [eq_refl] at a pair), and
 [tquot_unit_stripped] says the transposed identity is [id_cast] of
 its inverse, the shape of Theory/Equivalence/Strict.v's
 [lari_unit].
 - [tsub_adj Z f]: maps over X from [(Z, f)] into the unpackaged
 subspace ([tsub_hom], a setoid map into [S], continuous into the
 subspace, over [X]) against maps of the unlifted slice from
 [(Z, f)] to [(S, h)]; both directions are the identity on underlying
 maps ([tsub_adj_to_map] at [eq_refl]).  There is no object form of
 the subspace in [Top], so no counit.

 STRENGTHS.  [eq_refl]: [TQuot_carrier], [TQuot_open], [tquot_desc_map],
 [tstrip_under_lift], [tquot_adj_to_map], [tquot_adj_from_map],
 [tquot_obj_stripped_pair], [tsub_adj_to_map].  Leibniz by [destruct]:
 [tquot_obj_stripped], the file's one [Defined], and load-bearing:
 closed [Qed] in a scratch copy, it leaves [tquot_unit_stripped]
 refused (“Unable to unify”; Test/ProbeSubspace457.v's N25).  The
 openness lemmas of both constructions, [tsub_preimage_open] and the
 two universal properties close with [Qed], as Instance/Top.v's
 openness lemmas do; nothing here needs them transparent.  Up to [≈]:
 [tquot_adj_nat_l], [tquot_adj_nat_r], [tquot_unit_stripped].
 Type-valued equivalences ([↔], the library's [iffT]):
 [tquot_universal], [tsub_universal].

 UNIVERSES, read by [About] under [Set Printing Universes].
 - [tquot_open@{o}] has an empty block; [TQuot@{o}] carries [o <=
 projections.u0] and [o <= projections.u1], the stdlib caps of the
 pair projections its proofs use.
 - [tsub_open@{o o1}]: [o < o1]; [tsub_universal@{o o1 u}] adds
 [o < u], [u] the level of Instance/Top.v's [Continuous] (the hom
 level of [Top]), the [setoid_morphism_compose] caps, and the
 pair-projection caps [o <= projections.u0] and
 [o <= projections.u1].
 [tsub_hom@{o o1 h u}] and [tsub_adj@{o o1 h u u0}] relate the
 subspace's universe [o1] and the hom universe [h] of the given map
 not at all; [tsub_adj] is an [Isomorphism@{u0 o1 o1}], in
 [Sets@{o1 u0}].
 - [Top_Forget_over@{o h so}] and [Top_Forget_under@{o h so}]: [o <
 h], [h < so], [Top_Forget]'s own block, and stdlib caps.
 [TQuot_Functor@{o h so u}]: [o < h], [o < so], [h < u], the last
 Construction/Slice.v's strict bound at [Top@{h o}]'s hom level,
 then the stdlib projection bound [o < Projections.u0] (which
 [tquot_adj] carries too) and stdlib caps.
 [tquot_adj@{o h so u}] is an [Isomorphism@{u h h}], in [Sets@{h u}].
 No [Set] occurs in any block of this file: a word count of [Set] over
 the [About] output of all 69 of its constants (its [Print Module]
 listing, obligations included) reads 0.

 NOT DELIVERED.  The subspace as a [TopSpace] at any universe: at [o]
 it is refused as above, and at [o1] it is not attempted (argued, not
 measured: its union axiom, indexed at [o1], would need the union of
 [o]-valued witnessing opens of X over an index at [o1] to be an
 [o]-valued open); the packaged adjunctions, refused as above; naturality
 squares for [tsub_adj]; the object equation or counit on the subspace
 side; and any comparison with Instance/Top/Subspace.v's Prop-valued
 constructions (#1328's comparison functors). 

 --------
 Mac Lane，《为工作的数学家准备的范畴论》，第2版（GTM 5），§V.9，从页面图像中阅读：子空间和商空间的构造，书本第132-134页（PDF第141-143页）（目录ID maclane:V.9:construction2 和 maclane:V.9:construction3；书本编号都没有） nLab: https://ncatlab.org/nlab/show/subspace+topology nLab: https://ncatlab.org/nlab/show/quotient+space本文件的内容。Instance/Top/Subspace.v 说明了 Mac Lane 在 Instance/Top/Prop.v 的 Prop 值空间上的子空间和商构造，其中两个切片伴随都是 [Adjunction] 记录。该文件说明了其中哪些可以在该树自身的 Type 值 [Top]（Instance/Top.v）上形成，以及其余部分停止的位置。下面引用的每一个拒绝都是从针对该树编译的临时文件中读取的，通过在完整副本中一次移除一个命令的保护；Test/ProbeSubspace457.v 固定了六个（它的 N13、N14、N18、N20、N21 和 N25）。商在点的宇宙中适用。[tquot_open V] 仅适用于 [IsOpen X]，即沿着 [q] 的 [V] 的原像，因此它在点的宇宙 [o] 中有值，并且 [TQuot X T q : TopSpace@{o}] 是与 [X] 相同 [Top@{h o}] 的对象。它的开集合是那些开原像尊重 [T] 等式的 [V]，即 Instance/Top/Subspace.v 文件头中描述的集合加法。[tquot_universal] 是对任意空间 [Z] 的通用性质映射，两方向都适用，并且 [tquot_desc] 是书中的形式。子空间不行。[tsub_open V]，书中的谓语原文（“V 是 X 的开集沿 h 的原像”），对 X 的开集进行量化，并取值为 [o1]，[o < o1]。在 [Type@{o}] 时，同样的主体被拒绝，“宇宙不一致：无法强制 o < o 因为 o = o”；并且提供 [tsub_open] 作为 [IsOpen] 的 [TopSpace@{o}] 也被拒绝，“无法强制 o1 <= o 因为 o < o1”。因此子空间在 [o1] 以未封装的方式提供：Instance/Top.v 的记录的五条公理（[tsub_open_respects]、[tsub_open_proper]、[tsub_open_union] 及其索引 [o]，如 [open_union]、[tsub_open_whole]、[tsub_open_inter] 所示）、其外部的连续性 [h]（[tsub_preimage_open]）、来自某个空间 [tsub_continuous] 的集族映射到它的连续性，以及对任意空间 [Z] 映射进来的普遍性性质，两个方向（[tsub_universal]），以及书中的形式 [tsub_lift]。一种压缩的局部编码（V 中的一个点仅具有其像周围的 X 的开集，其原像位于 V 中）确实适合于 [TopSpace@{o}]，以 Instance/Top/CompHaus.v 的 [Top_sq_product] 风格。它未被显示为子空间拓扑，也未在此说明：它的开集包含书中的（Test/ProbeSubspace457.v 的 [p457_sq_global_to_local] 证明了对于尊重点相等的谓词的包含），但是其全称性质的“如果”部分——若两者相同则会随之而来——在尝试的两条路径中都被拒绝：将 squash 消除为 Type 值 [IsOpen Z] 时，“无法强制 o <= Prop”；以及通过压缩数据索引取并集时，“无法强制 o1 <= o 因为 o < o1”（#457 的该编码的侦查原型，在 Test/ProbeSubspace457.v 中重建，这些是其 N20 和 N21）。Instance/Top/CompHaus.v 记录了乘积的同样陷阱。OPEN 情况是不同的：Instance/Top/Presheaf.v 中的 [OpenSub U]，即开子集上的子空间，在点的宇宙上是 [TopSpace]，并且其对任意映射入空间的普遍性质成立；一个导入 Presheaf.v 的临时文件重新推导了 [sub_ext_recovers] 的“如果”部分，该部分在全局上下文下是闭合的。它在这里没有被导入：Presheaf.v 需要 stdlib reals。切片函子与置换。[Top_Forget_over X] 和 [Top_Forget_under X] 是 Mac Lane 在 Instance/Top/Forgetful.v 中的 G ↓ X 和 X ↓ G 的 [Top_Forget]，进入 LIFTED 的 [Sets@{h so}] 的切片，而 [Top_Forget] 落入其中。[TQuot_Functor X] 是 M，从 UNLIFTED 的 [Sets@{o so}] 的余切片进入 [Top@{h o}] 的余切片。伴随 [TQuot_Functor X ⊣ Top_Forget_under X] 被拒绝：它的函子从在 [o] 处有 Hom 的范畴到在 [h] 处有 Hom 的范畴，[Adjunction] 识别了其两个范畴的 Hom 等级（Theory/Adjunction.v，关于：[h1 = h2]），“无法强制 h = o 因为 o < h”。可构造的是 Forgetful.v 的阅读：作为跨宇宙同构的 Hom 集双射，小范畴由 Instance/Sets/Classifier.v 的 [Setoid_Lift] 提升。- [tquot_adj x y] ：在 [TQuot] 下的 X 映射与未提升的余切片映射到 [tstrip_under y] 对比，空间 [y] 被剥离为其点和基础映射（[Top_Forget_under X y] 是其提升，在 [eq_refl] 由 [tstrip_under_lift] 提供，不是函子像：从 [h] 的 Hom 到 [o] 的 Hom 的函子是 Forgetful.v 拒绝）。两个方向在基础映射上都是恒等的（[tquot_adj_to_map], [tquot_adj_from_map], 在 [eq_refl]）；[tquot_adj_nat_l] 和 [tquot_adj_nat_r] 是 [to] 所要求的两个自然性平方，[tstrip_under_map] 代替了忘记函子中的 [fmap]。[tquot_obj_stripped] 是 Mac Lane 的 “X ↓ G 在 M 之后是恒等”，去掉了（Leibniz, [Defined]；在一对处 [eq_refl]），并且 [tquot_unit_stripped] 表示转置的恒等是其逆的 [id_cast]，Theory/Equivalence/Strict.v 的形状 [lari_unit]。- [tsub_adj Z f]：从 [(Z, f)] 到解包子空间（[tsub_hom]，一个映射到 [S] 的集合同构图，连续映射到子空间，在 [X] 上）上对 X 的映射，针对从 [(Z, f)] 到 [(S, h)] 的未提升切片映射；两个方向在基础映射上都是恒等（[tsub_adj_to_map] 在 [eq_refl] 处）。在 [Top] 中没有子空间的对象形式，因此没有伴随元。优势。[eq_refl]：[TQuot_carrier]、[TQuot_open]、[tquot_desc_map]、[tstrip_under_lift]、[tquot_adj_to_map]、[tquot_adj_from_map]、[tquot_obj_stripped_pair]、[tsub_adj_to_map]。莱布尼茨由[destruct]：[tquot_obj_stripped]，文件的一份[Defined]，以及承重：闭合[Qed]在一个草稿副本中，它留下[tquot_unit_stripped]被拒绝（“无法统一”；Test/ProbeSubspace457.v 的 N25）。两种构造的开放性引理，[tsub_preimage_open] 和两个通用性质以 [Qed] 收尾，就像 Instance/Top.v 的开放性引理那样；这里不需要它们透明。至 [≈]：[tquot_adj_nat_l]、[tquot_adj_nat_r]、[tquot_unit_stripped]。类型值等价（[↔]，库的 [iffT]）：[tquot_universal]、[tsub_universal]。宇宙，由 [About] 在 [Set Printing Universes] 下读取。 - [tquot_open@{o}] 有一个空块；[TQuot@{o}] 携带 [o <= projections.u0] 和 [o <= projections.u1]，即其证明所使用的成对投影的标准库封装。 - [tsub_open@{o o1}] ：[o < o1]；[tsub_universal@{o o1 u}] 添加 [o < u]，[u] 为 Instance/Top.v 的 [Continuous] 的级别（[Top] 的同构级别）、[setoid_morphism_compose] 封装，以及成对投影封装 [o <= projections.u0] 和 [o <= projections.u1]。[tsub_hom@{o o1 h u}] 和 [tsub_adj@{o o1 h u u0}] 关联给定映射的子空间宇宙 [o1] 和同构宇宙 [h]；[tsub_adj] 是一个 [Isomorphism@{u0 o1 o1}]，在 [Sets@{o1 u0}] 中。 - [Top_Forget_over@{o h so}] 和 [Top_Forget_under@{o h so}] ：[o < h]，[h < so]，[Top_Forget] 自身的块，以及标准库封装。[TQuot_Functor@{o h so u}]：[o < h]，[o < so]，[h < u]，最后 Construction/Slice.v 在 [Top@{h o}] 的 hom 等级上的严格界限，然后是 stdlib 投影界限 [o < Projections.u0]（[tquot_adj] 也承担该界限）和 stdlib 上限。[tquot_adj@{o h so u}] 是一个 [Isomorphism@{u h h}]，在 [Sets@{h u}] 中。本文件的任何块中都没有出现 [Set]：对其 69 个常量的所有输出（包括其 [Print Module] 列表和义务）的 [About] 计数为 [Set] 时，结果为 0。未交付。在任何宇宙中，子空间作为 [TopSpace]：在 [o] 它如上所拒绝，而在 [o1] 则未尝试（讨论过，但未测量：其并集公理，索引在 [o1]，需要 [o] 值的见证开集在 [o1] 索引下的并集成为 [o] 值的开集）；打包的伴随，如上所拒绝；[tsub_adj] 的自然性方格；子空间侧的对象方程或余单位；以及与 Instance/Top/Subspace.v 的 Prop 值构造的任何比较（#1328 的比较函子）。
*)

#[local] Obligation Tactic := idtac.

(* Continuity depends on the map only up to pointwise [≈]. / 连续性仅依赖于地图直到逐点 [≈]。 *)
Lemma tcont_respects@{o +} {X Y : TopSpace@{o}}
  (f g : SetoidMorphism@{o o o} (top_carrier X) (top_carrier Y)) :
  (∀ x, f x ≈ g x) → Continuous X Y f → Continuous X Y g.
Proof.
  intros Hfg Hf U HU.
  apply (open_respects X (fun x => U (f x))); [|exact (Hf U HU)].
  intro x; split; intro u.
  - exact (open_proper Y U HU (f x) (g x) (Hfg x) u).
  - exact (open_proper Y U HU (g x) (f x) (symmetry (Hfg x)) u).
Qed.

(* * ** The quotient topology, at the points' universe / * ** 商拓扑，在点的宇宙中 *)

Section TopQuotient.

Universe o.

Context (X : TopSpace@{o}) (T : SetoidObject@{o o})
        (q : SetoidMorphism@{o o o} (top_carrier X) T).

(* It fits at [o]: it only APPLIES [IsOpen X]. / 它适用于 [o]：它仅适用于 [IsOpen X]。 *)
Definition tquot_open (V : T → Type@{o}) : Type@{o} :=
  ((∀ t t' : T, t ≈ t' → V t → V t') ∧ IsOpen X (fun x => V (q x)))%type.

Lemma tquot_open_respects (U V : T → Type@{o}) :
  (∀ t, U t ↔ V t) → tquot_open U → tquot_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros t t' e v. apply (fst (H t')), (Hp t t' e), (snd (H t)), v.
  - exact (open_respects X _ _ (fun x => H (q x)) Ho).
Qed.

Lemma tquot_open_proper (U : T → Type@{o}) :
  tquot_open U → ∀ t t' : T, t ≈ t' → U t → U t'.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma tquot_open_union (I : Type@{o}) (U : I → T → Type@{o}) :
  (∀ i, tquot_open (U i)) → tquot_open (fun t => { i : I & U i t }).
Proof.
  intro HU; split.
  - intros t t' e [i u]; exact (i; fst (HU i) t t' e u).
  - exact (open_union X I (fun i x => U i (q x)) (fun i => snd (HU i))).
Qed.

Lemma tquot_open_whole : tquot_open (fun _ => poly_unit@{o}).
Proof. split; [intros; exact ttt|exact (open_whole X)]. Qed.

Lemma tquot_open_inter (U V : T → Type@{o}) :
  tquot_open U → tquot_open V → tquot_open (fun t => U t ∧ V t).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros t t' e [u v]; exact (HpU t t' e u, HpV t t' e v).
  - exact (open_inter X _ _ HoU HoV).
Qed.

Definition TQuot : TopSpace@{o} := {|
  top_carrier   := T;
  IsOpen        := tquot_open;
  open_respects := tquot_open_respects;
  open_proper   := tquot_open_proper;
  open_union    := tquot_open_union;
  open_whole    := tquot_open_whole;
  open_inter    := tquot_open_inter
|}.

Example TQuot_carrier : top_carrier TQuot = T := eq_refl.

Example TQuot_open (V : T → Type@{o}) : IsOpen TQuot V = tquot_open V
  := eq_refl.

Lemma tquot_proj_cont : Continuous X TQuot q.
Proof. intros V HV; exact (snd HV). Qed.

Definition tquot_proj : ContinuousMorphism X TQuot :=
  @Build_ContinuousMorphism X TQuot q tquot_proj_cont.

(* The universal property, over ARBITRARY spaces [Z] mapping out. / 在任意空间 [Z] 上映射的泛性质。 *)
Lemma tquot_universal (Z : TopSpace@{o})
  (k : SetoidMorphism@{o o o} T (top_carrier Z)) :
  Continuous TQuot Z k ↔ Continuous X Z (setoid_morphism_compose k q).
Proof.
  split.
  - intros Hk W HW. exact (snd (Hk W HW)).
  - intros Hc W HW; split.
    + intros t t' e w.
      exact (open_proper Z W HW (k t) (k t') (proper_morphism k t t' e) w).
    + exact (Hc W HW).
Qed.

(* The book's form: a continuous [f : X → Z] whose underlying function factors as [k ∘ q] has [k] continuous out of the quotient. / 书的形式：一个连续的 [f : X → Z]，其底层函数分解为 [k ∘ q]，[k] 能从商中连续出来。 *)
Definition tquot_desc (Z : TopSpace@{o}) (f : ContinuousMorphism X Z)
  (k : SetoidMorphism@{o o o} T (top_carrier Z))
  (Hfk : ∀ x, continuous_map f x ≈ k (q x)) : ContinuousMorphism TQuot Z :=
  @Build_ContinuousMorphism TQuot Z k
    (snd (tquot_universal Z k)
       (tcont_respects (continuous_map f) (setoid_morphism_compose k q)
          Hfk (continuity f))).

Example tquot_desc_map (Z : TopSpace@{o}) (f : ContinuousMorphism X Z)
  (k : SetoidMorphism@{o o o} T (top_carrier Z))
  (Hfk : ∀ x, continuous_map f x ≈ k (q x)) :
  continuous_map (tquot_desc Z f k Hfk) = k := eq_refl.

End TopQuotient.

(* * ** The subspace topology, one universe up / * ** 子空间拓扑，超越一个宇宙 *)

Section TopSubspace.

Universes o o1.
Constraint o < o1.

Context (X : TopSpace@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S (top_carrier X)).

(* Mac Lane's predicate, verbatim: V is open when it is the preimage along [h] of an open of X. It quantifies over the opens of X, so it is valued at [o1], one universe above the points. / 麦克莱恩的谓词，逐字翻译：当 V 是沿着 [h] 的 X 的开集的原像时，V 是开集。它在 X 的开集上进行量化，因此它的取值在 [o1]，即比这些点高一个宇宙。 *)
Definition tsub_open (V : S → Type@{o}) : Type@{o1} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

Lemma tsub_open_respects (U V : S → Type@{o}) :
  (∀ s, U s ↔ V s) → tsub_open U → tsub_open V.
Proof.
  intros HUV [B [HB HUB]].
  exists B; split; [exact HB|].
  intro s; split.
  - intro v; exact (fst (HUB s) (snd (HUV s) v)).
  - intro b; exact (fst (HUV s) (snd (HUB s) b)).
Qed.

Lemma tsub_open_proper (U : S → Type@{o}) :
  tsub_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof.
  intros [B [HB HUB]] s t Hst u.
  apply (snd (HUB t)).
  exact (open_proper X B HB (h s) (h t) (proper_morphism h s t Hst)
           (fst (HUB s) u)).
Qed.

(* Unions indexed at the points' universe, as in [open_union]: the witnesses are data, and the union of the witnesses witnesses the union. / 在点的宇宙中索引的联合体，如 [open_union]：见证者是数据，联合体的见证者见证联合体。 *)
Lemma tsub_open_union (I : Type@{o}) (U : I → S → Type@{o}) :
  (∀ i, tsub_open (U i)) → tsub_open (fun s => { i : I & U i s }).
Proof.
  intro HU.
  exists (fun x => { i : I & `1 (HU i) x }); split.
  - apply (open_union X I (fun i => `1 (HU i))).
    intro i; exact (fst `2 (HU i)).
  - intro s; split.
    + intros [i u]; exact (i; fst (snd `2 (HU i) s) u).
    + intros [i b]; exact (i; snd (snd `2 (HU i) s) b).
Qed.

Lemma tsub_open_whole : tsub_open (fun _ => poly_unit@{o}).
Proof.
  exists (fun _ => poly_unit@{o}); split; [exact (open_whole X)|].
  intro s; split; exact (fun w => w).
Qed.

Lemma tsub_open_inter (U V : S → Type@{o}) :
  tsub_open U → tsub_open V → tsub_open (fun s => U s ∧ V s).
Proof.
  intros [A [HA HUA]] [B [HB HVB]].
  exists (fun x => A x ∧ B x); split.
  - exact (open_inter X A B HA HB).
  - intro s; split.
    + intros [u v]; exact (fst (HUA s) u, fst (HVB s) v).
    + intros [a b]; exact (snd (HUA s) a, snd (HVB s) b).
Qed.

(* [h] is continuous out of the subspace: preimages of opens are open. / [h] 是连续的超出子空间：开集的原像是开集。 *)
Lemma tsub_preimage_open (U : top_carrier X → Type@{o}) :
  IsOpen X U → tsub_open (fun s => U (h s)).
Proof.
  intro HU; exists U; split; [exact HU|].
  intro s; split; exact (fun w => w).
Qed.

(* Continuity into the subspace, for a setoid map from a space. / 从空间的集合映射到子空间的连续性。 *)
Definition tsub_continuous (Z : TopSpace@{o})
  (g : SetoidMorphism@{o o o} (top_carrier Z) S) : Type@{o1} :=
  ∀ V : S → Type@{o}, tsub_open V → IsOpen Z (fun z => V (g z)).

(* The universal property, over ARBITRARY spaces [Z] mapping in. / 在任意空间 [Z] 上的映射的通用性质。 *)
Lemma tsub_universal (Z : TopSpace@{o})
  (g : SetoidMorphism@{o o o} (top_carrier Z) S) :
  tsub_continuous Z g ↔ Continuous Z X (setoid_morphism_compose h g).
Proof.
  split.
  - intros Hc U HU.
    exact (Hc (fun s => U (h s)) (tsub_preimage_open U HU)).
  - intros Hc V [B [HB HVB]].
    apply (open_respects Z (fun z => B (h (g z)))).
    + intro z; split; [exact (snd (HVB (g z))) | exact (fst (HVB (g z)))].
    + exact (Hc B HB).
Qed.

(*
 The book's form: a continuous [f : Z → X] whose underlying function
 factors as [h ∘ g] has [g] continuous into the subspace. 

 --------
 书的形式：一个连续的 [f : Z → X]，其底层函数分解为 [h ∘ g]，[g] 连续映射到子空间。
*)
Definition tsub_lift (Z : TopSpace@{o}) (f : ContinuousMorphism Z X)
  (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (Hfg : ∀ z, continuous_map f z ≈ h (g z)) : tsub_continuous Z g :=
  snd (tsub_universal Z g)
    (tcont_respects (continuous_map f) (setoid_morphism_compose h g)
       Hfg (continuity f)).

End TopSubspace.

(* * ** The sliced forgetful functors at [Top_Forget] / * ** 在 [Top_Forget] 的切片遗忘函子 *)

(*
 [G ↓ X] and [X ↓ G] at [Top_Forget], into the slices of the LIFTED
 [Sets@{h so}] that [Top_Forget] lands in. 

 --------
 [G ↓ X] 和 [X ↓ G] 在 [Top_Forget]，进入 LIFTED [Sets@{h so}] 的片段中，[Top_Forget] 着陆其中。
*)
Program Definition Top_Forget_over@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :
  @Slice Top@{h o} X ⟶ @Slice Sets@{h so} (Top_Forget@{o h so} X) := {|
  fobj := fun x => (Top_Forget (`1 x); fmap[Top_Forget] (`2 x));
  fmap := fun x y m => (fmap[Top_Forget] (`1 m); _)
|}.
Next Obligation.
  intros X [a f] [b g] [m Hm] t; simpl in *. exact (Hm t).
Qed.
Next Obligation. intros X x y m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros X x t; simpl. apply reflexive_lift. Qed.
Next Obligation. intros X x y z m n t; simpl. apply reflexive_lift. Qed.

Program Definition Top_Forget_under@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :
  @Coslice Top@{h o} X ⟶ @Coslice Sets@{h so} (Top_Forget@{o h so} X) := {|
  fobj := fun x => (Top_Forget (`1 x); fmap[Top_Forget] (`2 x));
  fmap := fun x y m => (fmap[Top_Forget] (`1 m); _)
|}.
Next Obligation.
  intros X [a f] [b g] [m Hm] t; simpl in *. exact (Hm t).
Qed.
Next Obligation. intros X x y m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros X x t; simpl. apply reflexive_lift. Qed.
Next Obligation. intros X x y z m n t; simpl. apply reflexive_lift. Qed.

(* * ** The quotient functor, out of the UNLIFTED [Sets] / * ** 商函子，来自未提升的 [Sets] *)

Program Definition TQuot_Functor@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) :
  @Coslice Sets@{o so} (top_carrier X) ⟶ @Coslice Top@{h o} X := {|
  fobj := fun c => (TQuot X (`1 c) (`2 c); tquot_proj X (`1 c) (`2 c));
  fmap := fun c d m =>
    (@Build_ContinuousMorphism (TQuot X (`1 c) (`2 c)) (TQuot X (`1 d) (`2 d))
       (`1 m) _; _)
|}.
Next Obligation.
  intros X [T q] [T' q'] [m Hm]; simpl in *.
  apply (snd (tquot_universal X T q (TQuot X T' q') m)).
  apply (@tcont_respects X (TQuot X T' q') q'); [exact Hm|].
  exact (tquot_proj_cont X T' q').
Qed.
Next Obligation. intros X [T q] [T' q'] [m Hm] x; simpl in *. exact (Hm x). Qed.
Next Obligation. intros X c d m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros X c t; simpl. reflexivity. Qed.
Next Obligation. intros X c d e m n t; simpl. reflexivity. Qed.

(* * ** The cross-universe transpositions / * ** 跨宇宙转置 *)

Section Transpositions.

Universes o h so.
Constraint o < h.
Constraint o < so.

Context (X : TopSpace@{o}).

(* A space under [X], stripped to its points and underlying map in the UNLIFTED coslice; [Top_Forget_under] is its lift. / 在 [X] 下的一个空间，被剥离到其点和未提升余切片中的底图；[Top_Forget_under] 是它的提升。 *)
Definition tstrip_under (y : @Coslice Top@{h o} X) :
  @Coslice Sets@{o so} (top_carrier X) :=
  (top_carrier (`1 y); continuous_map (`2 y)).

(* The space's image under [Top_Forget_under X] is the lift of its stripped reading, on the nose. / 在 [Top_Forget_under X] 下，空间的图像是其剥离读数的提升，完全准确。 *)
Example tstrip_under_lift@{so' + | h < so' +} (y : @Coslice Top@{h o} X) :
  Top_Forget_under@{o h so'} X y
  = (Setoid_Lift@{o h} (`1 (tstrip_under y));
     SetoidMorphism_Lift@{o h} (`2 (tstrip_under y))) := eq_refl.

Definition tstrip_under_map {y z : @Coslice Top@{h o} X}
  (f : y ~{@Coslice Top@{h o} X}~> z) :
  tstrip_under y ~{@Coslice Sets@{o so} (top_carrier X)}~> tstrip_under z :=
  (continuous_map (`1 f); `2 f).

(*
 The transposition of [M ⊣ X ↓ G]: a map under [X] out of the quotient IS
 its underlying map.  The small side is lifted to sit beside [Top]'s large
 hom-setoid in one [Sets], as in Instance/Top/Forgetful.v's
 [discrete_adj]. 

 --------
 [M ⊣ X ↓ G] 的易位：在 [X] 下的映射在商下是其基础映射。小的一边被提升以位于 [Top] 的大同类集中，与 [Sets] 中一样，如 Instance/Top/Forgetful.v 的 [discrete_adj]。
*)
Program Definition tquot_adj (x : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice Top@{h o} X) (TQuot_Functor X x) y
     ; is_setoid := @homset (@Coslice Top@{h o} X) (TQuot_Functor X x) y |}
    (Setoid_Lift
       {| carrier := @hom (@Coslice Sets@{o so} (top_carrier X)) x
                       (tstrip_under y)
        ; is_setoid := @homset (@Coslice Sets@{o so} (top_carrier X)) x
                         (tstrip_under y) |}) := {|
  to   := {| morphism := fun k => (continuous_map (`1 k); `2 k) |};
  from := {| morphism := fun k =>
    (@Build_ContinuousMorphism (`1 (TQuot_Functor X x)) (`1 y) (`1 k) _;
     `2 k) |}
|}.
Next Obligation. intros x y k k' H t; exact (H t). Qed.
Next Obligation.
  intros [T q] [Y f] [k Hk]; simpl in *.
  apply (snd (tquot_universal X T q Y k)).
  apply (tcont_respects (continuous_map f)); [exact Hk|].
  exact (continuity f).
Qed.
Next Obligation. intros x y k k' H t; exact (H t). Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.

Example tquot_adj_to_map (x : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X)
  (k : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y) :
  `1 (to (tquot_adj x y) k) = continuous_map (`1 k) := eq_refl.

Example tquot_adj_from_map (x : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X)
  (k : x ~{@Coslice Sets@{o so} (top_carrier X)}~> tstrip_under y) :
  continuous_map (`1 (from (tquot_adj x y) k)) = `1 k := eq_refl.

Lemma tquot_adj_nat_l (x x' : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X)
  (f : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y)
  (g : x' ~{@Coslice Sets@{o so} (top_carrier X)}~> x) :
  to (tquot_adj x' y) (f ∘ fmap[TQuot_Functor X] g)
    ≈ to (tquot_adj x y) f ∘[@Coslice Sets@{o so} (top_carrier X)] g.
Proof. intro t; simpl. reflexivity. Qed.

Lemma tquot_adj_nat_r (x : @Coslice Sets@{o so} (top_carrier X))
  (y z : @Coslice Top@{h o} X) (f : y ~{@Coslice Top@{h o} X}~> z)
  (g : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y) :
  to (tquot_adj x z) (f ∘ g)
    ≈ tstrip_under_map f ∘[@Coslice Sets@{o so} (top_carrier X)]
        to (tquot_adj x y) g.
Proof. intro t; simpl. reflexivity. Qed.

(* [(X ↓ G) ∘ M = Id], stripped: Leibniz after destructing the pair. / [(X ↓ G) ∘ M = Id]，剥离后：莱布尼茨在摧毁这一对之后。 *)
Lemma tquot_obj_stripped (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under (TQuot_Functor X c) = c.
Proof. destruct c; reflexivity. Defined.

Example tquot_obj_stripped_pair (T : SetoidObject@{o o})
  (q : top_carrier X ~{Sets@{o so}}~> T) :
  tstrip_under (TQuot_Functor X (T; q)) = (T; q) := eq_refl.

(* The unit of the transposition is the identity, transported. / 换位的单位是被转移的本身。 *)
Lemma tquot_unit_stripped (c : @Coslice Sets@{o so} (top_carrier X)) :
  to (tquot_adj c (TQuot_Functor X c)) id
    ≈[@Coslice Sets@{o so} (top_carrier X)]
  id_cast (eq_sym (tquot_obj_stripped c)).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

End Transpositions.

Section SubspaceTransposition.

Universes o o1 h.
Constraint o < o1.
Constraint o < h.

Context (X : TopSpace@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S (top_carrier X)).

(*
 Maps over [X] from [(Z, f)] into the (unpackaged) subspace on [(S, h)]:
 setoid maps into [S], continuous into the subspace, over [X]. 

 --------
 将 [X] 上的映射从 [(Z, f)] 映射到 [(S, h)] 上的（未打包的）子空间：
 在 [X] 上映射到 [S] 的集合，连续映射到该子空间。
*)
Definition tsub_hom (Z : TopSpace@{o}) (f : ContinuousMorphism@{h o} Z X) :
  Type@{o1} :=
  { g : SetoidMorphism@{o o o} (top_carrier Z) S &
    (tsub_continuous X S h Z g ∧ (∀ z, continuous_map f z ≈ h (g z)))%type }.

Program Definition tsub_hom_setoid (Z : TopSpace@{o})
  (f : ContinuousMorphism@{h o} Z X) : SetoidObject@{o1 o1} := {|
  carrier := tsub_hom Z f;
  is_setoid := {| equiv := fun g g' => ∀ z, `1 g z ≈ `1 g' z |}
|}.
Next Obligation.
  intros Z f; constructor.
  - intros g z; reflexivity.
  - intros g g' H z; symmetry; exact (H z).
  - intros g g' g'' H1 H2 z; transitivity (`1 g' z);
      [exact (H1 z)|exact (H2 z)].
Qed.

(*
 The transposition of [G ↓ X ⊣ L]: a map over [X] into the subspace IS
 its underlying map, continuity coming from [tsub_universal]. 

 --------
 [G ↓ X ⊣ L] 的换位：一个关于 [X] 的映射到子空间 IS，其基础映射，连续性来源于 [tsub_universal]。
*)
Program Definition tsub_adj (Z : TopSpace@{o})
  (f : ContinuousMorphism@{h o} Z X) :
  @Isomorphism Sets
    (Setoid_Lift
       {| carrier := @hom (@Slice Sets@{o o1} (top_carrier X))
                       (top_carrier Z; continuous_map f) (S; h)
        ; is_setoid := @homset (@Slice Sets@{o o1} (top_carrier X))
                         (top_carrier Z; continuous_map f) (S; h) |})
    (tsub_hom_setoid Z f) := {|
  to   := {| morphism := fun k => (`1 k; (tsub_lift X S h Z f (`1 k) _, _)) |};
  from := {| morphism := fun g => (`1 g; _) |}
|}.
Next Obligation. intros Z f k z; simpl in *. symmetry; exact (`2 k z). Qed.
Next Obligation. intros Z f k z; simpl in *. symmetry; exact (`2 k z). Qed.
Next Obligation. intros Z f k k' H z; exact (H z). Qed.
Next Obligation.
  intros Z f g z; simpl in *. symmetry; exact (snd `2 g z).
Qed.
Next Obligation. intros Z f g g' H z; exact (H z). Qed.
Next Obligation. intros Z f g z; simpl. reflexivity. Qed.
Next Obligation. intros Z f k z; simpl. reflexivity. Qed.

Example tsub_adj_to_map (Z : TopSpace@{o}) (f : ContinuousMorphism@{h o} Z X)
  (k : @hom (@Slice Sets@{o o1} (top_carrier X))
         (top_carrier Z; continuous_map f) (S; h)) :
  `1 (to (tsub_adj Z f) k) = `1 k := eq_refl.

End SubspaceTransposition.
