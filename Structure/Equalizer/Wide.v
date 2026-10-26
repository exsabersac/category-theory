Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.

Generalizable All Variables.

(* * * Wide equalizers, elementarily: wide forks and descent / * * 宽频均衡器，基本上：宽叉和下降 *)

(*
 nLab:      https://ncatlab.org/nlab/show/equalizer
 nLab:      https://ncatlab.org/nlab/show/wide+pullback
 Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

 Mac Lane presents the coequalizer as a universal arrow over the walking
 parallel pair and then remarks that coequalizers of an ARBITRARY SET of
 parallel maps a → b are defined in the same way (Categories for the
 Working Mathematician, 2nd ed., §III.3, pp. 64-65).  This file and its
 dual [Structure/Coequalizer/Wide.v] carry out “the same way” on the
 limit side.  Given a family f : I → (x ~> y), a wide equalizer is an
 object q with a map e : q ~> x on which all the f i agree,

 ∀ i j,  f i ∘ e ≈ f j ∘ e,

 universal with that property: every h : z ~> x on which they agree
 factors uniquely through e.  Eckmann and Hilton defined equalizers for
 arbitrary families from the start, under the name “left equalizers”
 (Mathematische Annalen 151, 1963); the binary case of
 [Structure/Equalizer/Fork.v] is I = 2.

 WHAT IS DELIVERED, AND AT WHAT STRENGTH.

 - [IsWideEqualizer], the elementary record, is the literal
 generalization of [IsEqualizer]: one equation-family field and one
 descent field, no extra data.
 - [wide_equalizer_monic] and [wide_equalizer_unique] are the wide forms
 of [equalizer_monic] and [equalizer_unique].  Neither consumes an
 inhabitant of I; both hold for EVERY index type, empty included.
 - [wide_limit_equalizes] reads the fork equations off a limit.  It also
 needs no inhabitant.
 - The two ROUND TRIPS, [wide_equalizer_is_equalizer] and
 [is_wide_equalizer_limit], DO take an explicit inhabitant [i0 : I].
 They live in a section that fixes one.  For [is_wide_equalizer_limit]
 — the ELEMENTARY-to-LIMIT direction — that hypothesis is PROVED
 NECESSARY rather than assumed (see below).  For
 [wide_equalizer_is_equalizer], the LIMIT-to-ELEMENTARY direction, it
 is ASSUMED: nothing here refutes an unpointed version of it, and none
 is claimed.  The same asymmetry holds on the coequalizer side.

 WHY THE ROUND TRIPS NEED A POINT OF THE INDEX, and why that is a fact
 about the mathematics rather than about this proof.  A cone over
 [AWide fs] with apex z is a PAIR of legs, one into x and one into y,
 subject to [∀ i, f i ∘ legX ≈ legY].  When I is inhabited the second leg
 is determined by the first, and the cone condition collapses to the fork
 equations — which is what makes the elementary record equivalent to the
 limit.  When I is EMPTY the second leg is unconstrained, so a cone is
 just a pair of maps and the limit over the shape is the binary PRODUCT
 of x and y (an orientation, not a theorem — that identification is NOT
 formalized), while the elementary record, whose fork condition is then
 vacuous, is satisfied by [e := id[x]] and so pins down x itself.  The
 two notions come apart exactly there, and THAT is what is proved.  The
 binary donor never meets this because its index is [bool], and its
 [fork_legs] silently uses the distinguished member f:
 [fork_legs h ParY := f ∘ h].

 The necessity is machine-checked in three steps, all at the end of this
 file.  [wide_empty_id_IsWideEqualizer] exhibits the identity as an
 elementary wide equalizer over an empty index;
 [wide_unpointed_round_trip_gives_hom] shows that an unpointed round trip
 would therefore manufacture an arrow x ~> y out of nothing; and
 [wide_round_trip_needs_point] instantiates that at the walking arrow
 [Instance/Two.v]'s [_2], whose hom-set [TwoY ~> TwoX] is empty, deriving
 False.  So no reformulation of the PROOF removes the hypothesis; only a
 different elementary record (one carrying the second leg as data) would,
 and that record is not built here.

 UNIVERSES, measured in the constraint blocks rather than read off the
 binders (reproduce with [Set Printing Universes. About
 wide_equalizer_is_equalizer. About is_wide_equalizer_limit.]).  Both
 round trips come out over [C : Category@{u u0 u0}] with [I : Type@{u1}]
 and [u0 = u1]: the ambient hom and proof universes are identified, as
 they already are in the binary donor ([equalizer_is_equalizer] is over
 the same [Category@{u u0 u0}]), and the INDEX universe is identified
 with them as well.  Where the second identification ENTERS is measured,
 and it is NOT inherited from [Structure/Cone.v]: with the index and hom
 universes declared SEPARATELY, forming [Cone (AWide fs)] and writing
 [cone_leg N ParX] both yield only the BOUND [u1 <= u0], as do this
 file's own cone-building constants [wfork_cone],
 [is_wide_equalizer_cone] and [is_wide_equalizer_cone_ump].  The
 identification first appears at [wide_limit_equalizer_desc] below and at
 the assembly of the [Limit] record, both local to this file.  (An
 earlier draft of this header offered the [cone_leg] probe as evidence of
 inheritance; that probe collapses the two universes only under
 minimization, and the claim was wrong.  Whether any rearrangement of
 these proofs avoids the identification is UNTESTED.)  It also
 costs a consumer nothing, since a type at level l can be typed at any
 level above l, so the identification is satisfiable exactly when the
 [<=] form would be.  [IsWideEqualizer] ITSELF has an EMPTY constraint
 block, with the index universe free.

 CONSUMER.  [Theory/WeaklyInitial/Wide.v] runs Freyd's initial-object
 construction over [HasWideEqualizers], equalizing all endomorphisms of a
 product at once; it uses [wfork_eq] and [wide_equalizer_monic] and needs
 neither round trip, so it never meets the [i0] hypothesis.  It is an
 ADDITIVE second theorem: [Theory/WeaklyInitial.v] is untouched.

 NOT DELIVERED.  No second, leg-carrying elementary record that would
 round-trip unconditionally.  No identification of the limit over an
 empty-index wide shape with a binary product — the sharpness argument
 goes through an empty hom-set instead and needs no such theorem.  No
 [HasWideEqualizers] instance for any concrete category (the class is
 declared, not inhabited; the tree's only [HasEqualizers] inhabitant is
 [Sets_HasEqualizers], derived from completeness in Adjunction/GAFT.v,
 and no wide analogue is derived — so [Theory/WeaklyInitial/Wide.v] is a
 conditional exactly as its donor is).  No wide analogue of
 [Structure/Limit/Unique.v]'s leg-carrying essential
 uniqueness — [wide_equalizer_unique] delivers a bare [≅], exactly as its
 binary donor does.  No preservation or creation statements.  No
 comparison between the wide equalizer at I := bool and the binary
 equalizer of [Structure/Equalizer/Fork.v]: the SHAPES are compared, in
 [Instance/Parallel/Wide.v]'s [WideParallel_bool_Parallel] and
 [AWide_bool_APair], but the two elementary records are not related by
 any passage here. 

 --------
 nLab:       https://ncatlab.org/nlab/show/equalizer 
 nLab:       https://ncatlab.org/nlab/show/wide+pullback 
 维基百科:  https://en.wikipedia.org/wiki/Equaliser_(mathematics) 

 麦克莱恩将余共等化子呈现为在游走的平行对上的一个普遍箭头，然后指出任意集合的平行映射 a → b 的余共等化子定义方式相同（《为工作中的数学家而设的范畴论》，第二版，§III.3，第64-65页）。这个文件及其对偶 [Structure/Coequalizer/Wide.v] 在极限侧执行“相同方式”。给定一个族 f : I → (x ~> y)，宽等化子是一个对象 q，带有一个映射 e : q ~> x，使得所有 f i 在其上都一致，

 ∀ i j,  f i ∘ e ≈ f j ∘ e,具有该性质的通用对象：每个 h : z ~> x，它们在其上相等，都可以唯一地通过 e 分解。Eckmann 和 Hilton 从一开始就为任意族定义了等化器，称为“左等化器”（Mathematische Annalen 151, 1963）；[Structure/Equalizer/Fork.v] 的二元情况是 I = 2。

 交付的内容是什么，以及强度如何。- [IsWideEqualizer]，基本记录，是[IsEqualizer]的字面泛化：一个方程族字段和一个下降字段，没有额外数据。- [wide_equalizer_monic]和[wide_equalizer_unique]是[equalizer_monic]和[equalizer_unique]的宽形式。两者都不消耗I的元素；它们对每一种索引类型都成立，包括空类型。- [wide_limit_equalizes]从极限中读取分叉方程。它也不需要元素。- 两个往返，[wide_equalizer_is_equalizer]和[is_wide_equalizer_limit]，确实需要一个显式元素[i0 : I]。它们存在于一个固定了元素的截面中。对于[is_wide_equalizer_limit]——从基本到极限的方向——这个假设是被证明为必要的，而不是假定的（见下文）。对于[wide_equalizer_is_equalizer]——从极限到基本的方向——它是被假定的：这里没有什么否定非指点版本的，也没有声称有。同样的不对称也出现在共同化子的一边。为什么循环需要一个索引点，以及为什么这是关于数学的事实，而不是关于这个证明的事实。一个以顶点 z 为顶点的 [AWide fs] 圆锥是两条腿的组合，一条连接到 x，另一条连接到 y，并且受制于 [∀ i, f i ∘ legX ≈ legY]。当 I 有元素时，第二条腿由第一条腿决定，并且圆锥条件简化为分叉方程——这就是为什么基本记录等同于极限的原因。当 I 为空时，第二条腿不受约束，所以圆锥只是两张映射，形状上的极限就是 x 和 y 的二元乘积（这是定向，而不是定理——这种等同没有形式化），而基本记录，其分叉条件在这种情况下是空的，由 [e := id[x] 满足，因此确定了 x 本身。这两个概念正是在这里分离，并且这正是所证明的。二进制提供者从未遇到这个，因为它的索引是 [bool]，而它的 [fork_legs] 默默地使用了特殊成员 f: [fork_legs h ParY := f ∘ h]。

 该必要性在三个步骤中通过机器检验，全部在此文件的末尾。[wide_empty_id_IsWideEqualizer] 将身份展示为一个空索引上的基本宽等化器；[wide_unpointed_round_trip_gives_hom] 显示一个无指向的往返操作因此会凭空生成一个箭头 x ~> y；[wide_round_trip_needs_point] 在行走箭头 [Instance/Two.v] 的 [_2] 上实例化了这一点，其同构集 [TwoY ~> TwoX] 是空的，从而推导出 False。因此，没有任何 PROOF 的重述可以去掉假设；只有一个不同的基本记录（携带第二条腿作为数据）可以，而该记录在此未构建。UNIVERSES，是在约束块中测量的，而不是从绑定器中读取的（使用 [Set Printing Universes. 关于 wide_equalizer_is_equalizer. 关于 is_wide_equalizer_limit.] 重现）。两种往返操作的结果都出现在 [C : Category@{u u0 u0}] 上，并使用 [I : Type@{u1}] 和 [u0 = u1]：环境 hom 和证明 universes 被识别，就像它们在二进制源中已经是一样的（[equalizer_is_equalizer] 在相同的 [Category@{u u0 u0}] 上），并且 INDEX 宇宙也与它们识别相同。第二个识别 ENTERS 的测量是独立的，并且它不是从 [Structure/Cone.v] 继承的：当索引和 hom universes 单独声明时，形成 [Cone (AWide fs)]，并且写入 [cone_leg N ParX] 都只产生了 BOUND [u1 <= u0]，就像该文件自身的锥构建常数 [wfork_cone]、[is_wide_equalizer_cone] 和 [is_wide_equalizer_cone_ump] 一样。该标识首次出现在下方的 [wide_limit_equalizer_desc]，以及 [Limit] 记录的组合中，两者均在此文件的本地。（此标题的早期草稿提供了 [cone_leg] 探针作为继承的证据；该探针仅在最小化下合并两个宇宙，该说法是错误的。是否有任何重新排列这些证明的方法可以避免该标识尚未测试。）它对消费者也没有任何成本，因为级别为 l 的类型可以在任何高于 l 的级别上进行类型化，因此该标识在 [<=] 形式可满足时恰好可满足。[IsWideEqualizer] 本身有一个空的约束块，索引宇宙是自由的。消费者。[Theory/WeaklyInitial/Wide.v] 在 [HasWideEqualizers] 上运行 Freyd 的初始对象构造，一次性将积的所有自同态等化；它使用 [wfork_eq] 和 [wide_equalizer_monic]，并且不需要往返，因此它从未遇到 [i0] 假设。这是一个加法的第二定理：[Theory/WeaklyInitial.v] 保持不变。未交付。没有第二个、携带弯腿的基本记录可以无条件地往返。没有在空索引宽形状上通过二元积识别极限——尖锐性论证转而通过空同态集，并且不需要这样的定理。对于任何具体范畴没有 [HasWideEqualizers] 实例（该类已声明，但没有元素；树的唯一 [HasEqualizers] 元素是 [Sets_HasEqualizers]，由 Adjunction/GAFT.v 中的完备性推导而来，并未推导出广义对应物——所以 [Theory/WeaklyInitial/Wide.v] 正如其源对应物一样是条件的）。没有 [Structure/Limit/Unique.v] 的携带弯腿的基本唯一性的广义对应物——[wide_equalizer_unique] 仅提供一个空 [≅]，就像其二元源对应物一样。没有保持或生成的陈述。在 I := bool 处的宽等化器与 [Structure/Equalizer/Fork.v] 的二进制等化器之间没有可比性：在 [Instance/Parallel/Wide.v] 的 [WideParallel_bool_Parallel] 和 [AWide_bool_APair] 中比较了形状，但这两个基本记录在此处没有通过任何方式相关联。
*)

(* The wide equalizer of a diagram of shape [WideParallel I]: a terminal cone, exactly as [Structure/Equalizer.v]'s [Equalizer] is over the two-arrow shape. / 形状 [WideParallel I] 的图表的宽等化器：一个端锥，正如 [Structure/Equalizer.v] 的 [Equalizer] 在双箭头形状上所示。 *)
Definition WideEqualizer {C : Category} {I : Type} (F : WideParallel I ⟶ C) :=
  Limit F.

(*
 The elementary universal property: [e] equalizes the whole family at q,
 and every map h into x that the family agrees on factors uniquely
 through e. 

 --------
 基本的泛性质：[e] 在 q 上将整个族等化，且每个映射 h 到 x，若该族在其上相等，则唯一地通过 e 分解。
*)
Record IsWideEqualizer {C : Category} {I : Type} {x y : C}
  (fs : I → x ~> y) (q : C) (e : q ~> x) := {
  (* every member of the family absorbs e in the same way / 家庭中的每个成员以相同的方式吸收 E *)
  wfork_eq : ∀ i j : I, fs i ∘ e ≈ fs j ∘ e;

  (* universal property: every jointly forking map h factors uniquely / 泛性质：每个共同分叉映射 h 都有唯一分解 *)
  weq_desc {z} (h : z ~> x) (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
    ∃! u : z ~> q, e ∘ u ≈ h
}.

Arguments wfork_eq {_ _ _ _ _ _ _} _ _ _.
Arguments weq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(*
 A category has all wide equalizers when every family of parallel arrows
 carries an elementary wide equalizer.  The index [Type] is a universe
 PARAMETER of the class, not a quantifier over every universe, exactly as
 for [Structure/Limit/Product.v]'s indexed products; a consumer whose
 index is a hom-type instantiates it there. 

 --------
 当每个平行箭头族都具有一个基本的广义等化器时，一个范畴具有所有广义等化器。指数 [Type] 是该类的一个宇宙参数，而不是对每个宇宙的量化器，正如 [Structure/Limit/Product.v] 的索引积一样；其指数是同态类型的消费者在此处实例化它。
*)
Class HasWideEqualizers (C : Category) := {
  wide_equalizer {I : Type} {x y : C} (fs : I → x ~> y) :
    ∃ (q : C) (e : q ~> x), IsWideEqualizer fs q e
}.

Section WideEqualizerLimit.

Context {C : Category}.
Context {I : Type}.
Context {x y : C}.
Context (fs : I → x ~> y).

(* Abbreviations for the diagram and its shape; these are notations, so the statements below are literally about [AWide fs] and [WideParallel I]. / 图表及其形状的缩写；这些是符号，所以下面的陈述字面上是关于 [AWide fs] 和 [WideParallel I] 的。 *)
Local Notation WFam := (AWide fs).
Local Notation WShape := (WideParallel I).

(* * ** Wide equalizing maps are monomorphisms / * ** 广义均衡映射是单射 *)

(*
 The binary argument verbatim: both factorizations of e ∘ g1 agree with
 the canonical one, so descent uniqueness cancels e on the left.  No
 member of the family is ever named, so no inhabitant of I is needed. 

 --------
 二进制参数逐字：e ∘ g1 的两个分解都与标准分解一致，因此下降唯一性在左边抵消了 e。该族的任何成员都未被命名，因此不需要 I 的任何元素。
*)
Lemma wide_equalizer_monic {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : Monic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : ∀ i j : I, fs i ∘ (e ∘ g1) ≈ fs j ∘ (e ∘ g1)).
  { intros i j.
    rewrite !comp_assoc.
    rewrite (wfork_eq E i j).
    reflexivity. }
  transitivity (unique_obj (weq_desc E (e ∘ g1) Hfork)).
  - symmetry.
    apply (uniqueness (weq_desc E (e ∘ g1) Hfork)).
    reflexivity.
  - apply (uniqueness (weq_desc E (e ∘ g1) Hfork)).
    symmetry.
    exact Hg.
Qed.

(* * ** Wide equalizers are unique up to isomorphism / * ** 宽均衡器在同构下是唯一的 *)

Lemma wide_equalizer_unique {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsWideEqualizer fs q1 e1) (E2 : IsWideEqualizer fs q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (weq_desc E2 e1 (wfork_eq E1)) as D12.
  pose proof (weq_desc E1 e2 (wfork_eq E2)) as D21.
  pose proof (weq_desc E1 e1 (wfork_eq E1)) as D11.
  pose proof (weq_desc E2 e2 (wfork_eq E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D22).
      apply id_right.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D11).
      apply id_right.
Defined.

(* * ** From the limit presentation to the fork equations / * ** 从极限表示到叉式方程 *)

(*
 The limit leg over [ParX] is equalized by the whole family: every member
 pushes it to the leg over [ParY], by leg coherence at that member — the
 arrow [i] of the shape IS the index, and [fmap[AWide fs] i] IS [fs i].
 No inhabitant of I is needed: the statement quantifies over i and j. 

 --------
 通过整个家族将 [ParX] 上的极限腿进行平衡：每个成员通过该成员的腿一致性将其推向 [ParY] 上的腿——形状的箭头 [i] 是索引，并且 [fmap[AWide fs] i] 是 [fs i]。不需要 I 的任何居民：该陈述对 i 和 j 进行量化。
*)
Lemma wide_limit_equalizes (L : WideEqualizer WFam) :
  ∀ i j : I,
    fs i ∘ limit_leg (limit_is_alimit L) ParX
      ≈ fs j ∘ limit_leg (limit_is_alimit L) ParX.
Proof.
  intros i j.
  transitivity (limit_leg (limit_is_alimit L) ParY).
  - exact (limit_leg_coherence (limit_is_alimit L)
             (i : ParX ~{WShape}~> ParY)).
  - symmetry.
    exact (limit_leg_coherence (limit_is_alimit L)
             (j : ParX ~{WShape}~> ParY)).
Qed.

(* * ** The round trips, over a chosen member of the family / * ** 往返，经过家庭中选定的成员 *)

Section Pointed.

(*
 A chosen index.  This is the hypothesis the two round trips need, and
 the section is exactly its scope: everything above holds without it, and
 the sharpness results below show nothing weaker will do. 

 --------
 一个选定的索引。这是两个往返所需要的假设，且该部分正是其范围：其上面的所有内容在没有它的情况下仍然成立，而下面的锐性结果显示没有更弱的假设是不行的。
*)
Context (i0 : I).

(*
 The legs of the cone induced by a jointly forking map h: the leg over
 [ParX] is h itself, the leg over [ParY] the common composite through the
 chosen member. 

 --------
 由联合分叉映射 h 引起的圆锥的腿：在 [ParX] 上的腿是 h 本身，在 [ParY] 上的腿是通过所选成员的公共合成。
*)
Definition wfork_legs {z : C} (h : z ~> x) (p : ParObj) :
  z ~{C}~> WFam p :=
  match p return (z ~{C}~> WFam p) with
  | ParX => h
  | ParY => fs i0 ∘ h
  end.

(* Leg coherence. This statement is definitionally the [cone_coherence] field of an [ACone] over [AWide fs]. / 腿部相干性。这个陈述从定义上来说是 [cone_coherence] 在 [AWide fs] 上的 [ACone] 的范畴。 *)
Lemma wfork_legs_coherence {z : C} (h : z ~> x)
  (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
  ∀ (a b : ParObj) (k : a ~{WShape}~> b),
    fmap[WFam] k ∘ wfork_legs h a ≈ wfork_legs h b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - (* the identity arrow on ParX / ParX 上的身份箭头 *)
    apply id_left.
  - (* the arrow k : I, sent to fs k / 箭头 k : I，发送到 fs k *)
    exact (Hh k i0).
  - (* an arrow ParY ~> ParX: refuted by the empty hom-set / 一个箭头 ParY ~> ParX：被空同态集驳斥 *)
    destruct k.
  - (* the identity arrow on ParY / ParY 上的身份箭头 *)
    apply id_left.
Qed.

Definition wfork_cone {z : C} (h : z ~> x)
  (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) : Cone WFam :=
  @Build_Cone WShape C WFam z
    (@Build_ACone WShape C z WFam
       (wfork_legs h) (wfork_legs_coherence h Hh)).

(* Descent through the limit apex. / 通过极点的下降。 *)
Lemma wide_limit_equalizer_desc (L : WideEqualizer WFam)
  {z : C} (h : z ~> x) (Hh : ∀ i j : I, fs i ∘ h ≈ fs j ∘ h) :
  ∃! u : z ~> L, limit_leg (limit_is_alimit L) ParX ∘ u ≈ h.
(*
 Lib.v sets [Default Proof Using “Type”], which keeps only the section
 variables occurring in the STATEMENT.  This is the ONE proof in the
 section that reaches for [i0] without its statement mentioning it — the
 others go through [wfork_legs], whose body carries the dependency. 

 --------
 Lib.v 设置了 [Default Proof Using “Type”]，它只保留出现在 STATEMENT 中的节变量。这是该节中唯一一个在其语句未提及的情况下使用 [i0] 的证明——其他的证明则通过 [wfork_legs]，其中的主体携带依赖性。
*)
Proof using All.
  unshelve eapply Build_Unique.
  - exact (limit_med (limit_is_alimit L) (wfork_cone h Hh)).
  - exact (limit_med_commutes
             (limit_is_alimit L) (wfork_cone h Hh) ParX).
  - intros v Hv.
    refine (limit_med_unique
              (limit_is_alimit L) (wfork_cone h Hh) v _).
    intros p.
    destruct p.
    + exact Hv.
    + (* the ParY leg follows from the ParX leg via coherence at i0 / 通过 i0 的相干性，ParY 腿从 ParX 腿推导而来 *)
      rewrite <- (limit_leg_coherence (limit_is_alimit L)
                    (i0 : ParX ~{WShape}~> ParY)).
      rewrite <- comp_assoc.
      rewrite Hv.
      reflexivity.
Qed.

(* A limit of [AWide fs] is an elementary wide equalizer at its apex. / [AWide fs] 的极限是在其顶点的一个基本宽频均衡器。 *)
Definition wide_equalizer_is_equalizer (L : WideEqualizer WFam) :
  IsWideEqualizer fs L (limit_leg (limit_is_alimit L) ParX) :=
  {| wfork_eq  := wide_limit_equalizes L
   ; weq_desc  := fun z h Hh => wide_limit_equalizer_desc L h Hh |}.

(* * ** From the elementary presentation back to the limit / * ** 从初步展示回到极限 *)

Definition is_wide_equalizer_cone {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : Cone WFam :=
  wfork_cone e (wfork_eq E).

(*
 The universal property of that cone; definitionally the [ump_limits]
 field of the limit whose limit cone is [is_wide_equalizer_cone]. 

 --------
 那个锥体的普遍性质；从定义上讲，是极限的 [ump_limits] 域，其极限锥体是 [is_wide_equalizer_cone] 。
*)
Lemma is_wide_equalizer_cone_ump {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) (N : Cone WFam) :
  ∃! u : vertex_obj[N] ~> q,
    ∀ p : ParObj, wfork_legs e p ∘ u ≈ cone_leg N p.
Proof.
  assert (HX : ∀ i : I, fs i ∘ cone_leg N ParX ≈ cone_leg N ParY).
  { intro i.
    exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _
             (i : ParX ~{WShape}~> ParY)). }
  assert (Hfs : ∀ i j : I, fs i ∘ cone_leg N ParX ≈ fs j ∘ cone_leg N ParX).
  { intros i j.
    rewrite (HX i).
    rewrite (HX j).
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (weq_desc E (cone_leg N ParX) Hfs)).
  - intros p.
    destruct p.
    + exact (unique_property (weq_desc E (cone_leg N ParX) Hfs)).
    + (* the leg over ParY: (fs i0 ∘ e) ∘ u ≈ nY via the ParX triangle / 腿在 ParY 上: (fs i0 ∘ e) ∘ u ≈ nY 通过 ParX 三角形 *)
      simpl.
      rewrite <- comp_assoc.
      rewrite (unique_property (weq_desc E (cone_leg N ParX) Hfs)).
      exact (HX i0).
  - intros v Hv.
    apply (uniqueness (weq_desc E (cone_leg N ParX) Hfs)).
    exact (Hv ParX).
Qed.

(* An elementary wide equalizer yields the bundled limit over the wide shape. / 一个初级宽频均衡器在宽形状上产生了捆绑极限。 *)
Definition is_wide_equalizer_limit {q : C} {e : q ~> x}
  (E : IsWideEqualizer fs q e) : WideEqualizer WFam :=
  {| limit_cone := is_wide_equalizer_cone E
   ; ump_limits := fun N => is_wide_equalizer_cone_ump E N |}.

End Pointed.

(* * ** The inhabitant is necessary, not merely convenient / * ** 居民是必要的，而不仅仅是方便的 *)

(*
 Over an empty index the fork condition is vacuous, so the identity of x
 satisfies the elementary record — descent is then just [id_left], and
 needs no emptiness at all. 

 --------
 在一个空索引上，分叉条件是无意义的，因此 x 的身份满足基本记录——下降只是 [id_left]，并且根本不需要空性。
*)
Lemma wide_empty_id_IsWideEqualizer (Hempty : I → False) :
  IsWideEqualizer fs x id[x].
Proof.
  unshelve refine {| wfork_eq := _ |}.
  - intros i j; destruct (Hempty i).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact h.
    + apply id_left.
    + intros v Hv.
      rewrite <- Hv.
      apply id_left.
Defined.

End WideEqualizerLimit.

(*
 Consequently an UNPOINTED round trip — one turning any elementary wide
 equalizer into a limit of the same diagram AT THAT SAME APEX, with no
 member of the family in hand — would produce an arrow x ~> y out of
 nothing: apply it to the identity above and read off the limit leg over
 [ParY].  The apex is pinned by the hypothesis below ([IsALimit (AWide fs)
 q]), which makes the refuted principle strictly stronger than the literal
 unpointed form of what is delivered, [is_wide_equalizer_limit] returning a
 [WideEqualizer WFam] whose apex its type does not pin. 

 --------
 因此，一个无指向的往返——将任何基本宽等化器转化为同一图在同一顶点处的一个极限，而手中没有该族的任何成员——将会凭空产生一个箭头 x ~> y：将其应用于上面的恒等式，并读取 [ParY] 上的极限腿。根据下面的假设（[IsALimit (AWide fs) q]），顶点被固定，这使得被驳斥的原则比所给出的无指向形式严格更强，[is_wide_equalizer_limit] 返回一个 [WideEqualizer WFam]，其顶点类型没有固定。
*)
Definition wide_unpointed_round_trip_gives_hom
  {C : Category} {I : Type} {x y : C} (fs : I → x ~> y)
  (Hempty : I → False)
  (RT : ∀ (q : C) (e : q ~> x),
          IsWideEqualizer fs q e → IsALimit (AWide fs) q) :
  x ~{C}~> y :=
  limit_leg (RT x id[x] (wide_empty_id_IsWideEqualizer fs Hempty)) ParY.

(*
 And that is refutable.  The witness is the walking arrow: [_2] has no
 arrow from [TwoY] to [TwoX] at all, so an unpointed round trip over the
 empty family [TwoY ⇉ TwoX] would produce an inhabitant of an empty
 hom-set.  This is the sharpness statement for the [i0] hypothesis of the
 section above; the general shape of the refuted principle is
 [wide_unpointed_round_trip_gives_hom], and this is one instance of it. 

 --------
 这是可以反驳的。证人是行进的箭：[_2] 从 [TwoY] 到 [TwoX] 根本没有箭，所以在空的族 [TwoY ⇉ TwoX] 上一个未指向的往返将产生一个空同集的元素。这是上述部分 [i0] 假设的尖锐性陈述；被反驳原理的一般形式是 [wide_unpointed_round_trip_gives_hom]，而这就是其中的一个实例。
*)
Definition two_empty_family : Empty_set → (TwoY ~{_2}~> TwoX) :=
  fun i => match i with end.

Theorem wide_round_trip_needs_point :
  (∀ (q : _2) (e : q ~{_2}~> TwoY),
     IsWideEqualizer two_empty_family q e
     → IsALimit (AWide two_empty_family) q) → False.
Proof.
  intro RT.
  exact (TwoHom_Y_X_absurd
           (wide_unpointed_round_trip_gives_hom two_empty_family
              (fun i => match i with end) RT)).
Qed.
