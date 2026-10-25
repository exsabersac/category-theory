Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 Subobject classifiers.

 nLab:      https://ncatlab.org/nlab/show/subobject+classifier
 Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

 In a category with a terminal object and pullbacks, a subobject classifier
 is an object Ω together with a point [truth : 1 ~> Ω] such that every
 monomorphism m : u ~> x arises, in exactly one way, as the pullback of
 [truth] along a characteristic morphism [char m : x ~> Ω]:

 u ---!---> 1
 |          |
 m|          | truth
 v          v
 x --char-> Ω

 The data below packages the characteristic morphism as an operation
 [char], respecting the subobject equivalence of Theory/Subobject.v, with
 the square above a pullback ([char_pullback]) and unique among morphisms
 classifying m ([char_unique]).  The classification theorem
 [classifier_classifies] then exhibits the setoid of subobjects of x as
 isomorphic in Sets to the hom-setoid x ~> Ω, the backward map being
 pullback of [truth] via the reindexing of Theory/Subobject/Functor.v. 

 --------
 子对象分类器。

 nLab:       https://ncatlab.org/nlab/show/subobject+classifier 
 维基百科:  https://en.wikipedia.org/wiki/Subobject_classifier 

 在具有终对象和拉回的范畴中，子对象分类器是一个对象 Ω，
 并且有一个点 [truth : 1 ~> Ω]，使得每个单射 m : u ~> x 都以唯一的方式
 作为沿着特征态射 [char m : x ~> Ω] 的拉回出现：

 u ---!---> 1
 |          |
 m|          | 真值
 v          v
 x --char-> Ω下面的数据将特征态射打包为一个运算 [char]，同时尊重 Theory/Subobject.v 的子对象等价关系，上面的方形是一个拉回（[char_pullback]），在分类 m 的态射中是唯一的（[char_unique]）。分类定理 [classifier_classifies] 随后展示了 x 的子对象的集合组织在 Sets 中同构于函子集合 x ~> Ω，反向映射则是通过 Theory/Subobject/Functor.v 的重索引对 [truth] 进行拉回。
*)

Section SubobjectClassifier.

Context {C : Category}.
Context `{HT : @Terminal C}.
Context `{HP : @HasPullbacks C}.

Class SubobjectClassifier := {
  Ω : C;                                (* the object of truth values / 真值的对象 *)
  truth : 1 ~> Ω;                       (* the generic subobject / 通用子对象 *)

  (* the characteristic morphism of a mono m : u ~> x / 单射 m : u ~> x 的特征态射 *)
  char {u x : C} (m : u ~> x) (M : Monic m) : x ~> Ω;

  (* the classifying square is a pullback of truth along char m / 分类平方是沿着特征 m 的真理的拉回 *)
  char_pullback {u x : C} (m : u ~> x) (M : Monic m) :
    IsPullback (char m M) truth u m one;

  (* and char m is the unique morphism with that property / 并且 char m 是具有该性质的唯一态射 *)
  char_unique {u x : C} (m : u ~> x) (M : Monic m) (h : x ~> Ω) :
    IsPullback h truth u m one → h ≈ char m M
}.

Context `{HS : SubobjectClassifier}.

(*
 truth is monic, trivially: its domain is terminal, so any two morphisms
 z ~> 1 already agree by one_unique, before truth is even applied. 

 --------
 真理是单一的，这很简单：它的定义域是终端对象，所以任何两个态射 z ~> 1 已经通过 one_unique 相互一致，甚至在应用真理之前。
*)
Lemma truth_monic : Monic truth.
Proof.
  constructor.
  intros z g1 g2 _.
  apply one_unique.
Qed.

(* The generic subobject: truth as a subobject of Ω. / 泛型子对象：Ω 的子对象——真理。 *)
Definition truth_subobject : SubObj Ω := {|
  sub_dom      := 1;
  sub_mono     := truth;
  sub_is_monic := truth_monic
|}.

(*
 A pullback square is stable under replacing its second projection by an
 ≈-equal morphism; both fields transport by rewriting.  Companion to
 [is_pullback_respects_left] of Theory/Subobject/Functor.v, used below to
 trade the chosen projection into 1 for the canonical [one]. 

 --------
 当将拉回方的第二投影替换为一个≈-等价的态射时，它是稳定的；两个域通过重写进行传递。这是Theory/Subobject/Functor.v中[is_pullback_respects_left]的伴随，用于下面将选定的投影换成1以得到规范的[one]。
*)
Lemma is_pullback_respects_snd {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 p2' : P ~> y} (Hp : p2 ≈ p2') :
  IsPullback f g P p1 p2 → IsPullback f g P p1 p2'.
Proof.
  intros [Hc Hu].
  constructor.
  - now rewrite <- Hp.
  - intros Q q1 q2 Hq.
    pose proof (Hu Q q1 q2 Hq) as U.
    destruct (unique_property U) as [U1 U2].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * exact U1.
      * now rewrite <- Hp.
    + intros v [Hv1 Hv2].
      apply (uniqueness U); split.
      * exact Hv1.
      * now rewrite Hp.
Qed.

(*
 A pullback square transports across an isomorphism of its apex: given a
 pullback with apex P and an isomorphism i : P' ≅ P, precomposing the two
 projections with [to i] yields a pullback with apex P'.  The two extra
 equalities let the caller name the transported projections directly.
 Companion to [is_pullback_respects_snd] above and
 [is_pullback_respects_left] of Theory/Subobject/Functor.v. 

 --------
 一个拉回方将其顶点跨同构进行运算：给定一个顶点为 P 的拉回和一个同构 i : P' ≅ P，将两个投影与 [to i] 预组合会得到顶点为 P' 的拉回。两个额外的等式允许调用者直接命名被运送的投影。它是上文 [is_pullback_respects_snd] 的对应物，以及 Theory/Subobject/Functor.v 中 [is_pullback_respects_left] 的对应物。
*)
Lemma is_pullback_precompose_iso {A B Z : C} {f : A ~> Z} {g : B ~> Z}
      {P P' : C} {p1 : P ~> A} {p2 : P ~> B} (i : P' ≅ P)
      {p1' : P' ~> A} {p2' : P' ~> B}
      (H1 : p1 ∘ to i ≈ p1') (H2 : p2 ∘ to i ≈ p2') :
  IsPullback f g P p1 p2 → IsPullback f g P' p1' p2'.
Proof.
  intros Hpb.
  assert (E1 : p1' ∘ from i ≈ p1).
  { rewrite <- H1, <- comp_assoc, iso_to_from; cat. }
  assert (E2 : p2' ∘ from i ≈ p2).
  { rewrite <- H2, <- comp_assoc, iso_to_from; cat. }
  constructor.
  - rewrite <- H1, <- H2, !comp_assoc.
    now rewrite (is_pullback_commutes Hpb).
  - intros Q q1 q2 Hq.
    pose proof (is_pullback_ump Hpb Q q1 q2 Hq) as U.
    destruct (unique_property U) as [U1 U2].
    unshelve refine {| unique_obj := from i ∘ unique_obj U |}.
    + split.
      * now rewrite comp_assoc, E1.
      * now rewrite comp_assoc, E2.
    + intros v [Hv1 Hv2].
      assert (Hvw : unique_obj U ≈ to i ∘ v).
      { apply (uniqueness U); split;
          [ now rewrite comp_assoc, H1
          | now rewrite comp_assoc, H2 ]. }
      rewrite Hvw, comp_assoc, iso_from_to.
      now rewrite id_left.
Qed.

(*
 [char] respects the subobject equivalence of Theory/Subobject.v.  This
 was formerly a class field; it is derivable from [char_pullback] and
 [char_unique] (transport the classifying square of m' across the domain
 isomorphism, then invoke uniqueness), so it is proved here once rather
 than paid as a redundant obligation by every instance. 

 --------
 [char] 尊重 Theory/Subobject.v 的子对象等价性。这以前是一个类字段；它可以从 [char_pullback] 和 [char_unique] 推导出来（通过域同构传递 m' 的分类方阵，然后调用唯一性），因此这里只证明一次，而不是由每个实例作为重复的义务来处理。
*)
Lemma char_respects {u u' x : C} (m : u ~> x) (M : Monic m)
      (m' : u' ~> x) (M' : Monic m') :
  {| sub_dom := u; sub_mono := m; sub_is_monic := M |}
    ≈ {| sub_dom := u'; sub_mono := m'; sub_is_monic := M' |}
  → char m M ≈ char m' M'.
Proof.
  intros [i Hi]; simpl in Hi.
  symmetry.
  apply char_unique.
  apply (is_pullback_precompose_iso i Hi (one_unique (one ∘ to i) one)).
  exact (char_pullback m' M').
Qed.

(*
 Round trip (i): classifying the pullback of truth along h recovers h.
 The chosen pullback square, with its projection into 1 traded for [one],
 is a classifying square for h, so char_unique concludes. 

 --------
 往返 (i)：沿 h 对真理的拉回的分类可以恢复 h。
 所选择的拉回方格，其投影到 1 被转换为 [one]，
 是 h 的分类方格，因此 char_unique 得出结论。
*)
Lemma classifier_char_roundtrip {x : C} (h : x ~> Ω) :
  char (sub_mono (sub_reindex h truth_subobject))
       (sub_is_monic (sub_reindex h truth_subobject)) ≈ h.
Proof.
  symmetry.
  apply char_unique.
  apply (is_pullback_respects_snd
           (one_unique (pullback_snd h truth (pullback h truth)) one)).
  exact (pullback_is_pullback h truth (pullback h truth)).
Qed.

(*
 Round trip (ii): pulling truth back along char m recovers the subobject
 (u, m) up to the SubObj equivalence, since the classifying square is
 itself a pullback of truth along char m; any two pullbacks of one cospan
 agree, via sub_reindex_transport. 

 --------
 往返（ii）：沿着 char m 拉回真值可以恢复子对象 (u, m)（到 SubObj 等价类），因为分类平方本身就是沿 char m 的真值的拉回；一个余锥的任意两个拉回通过 sub_reindex_transport 是一致的。
*)
Lemma classifier_pullback_roundtrip {x : C} (s : SubObj x) :
  sub_reindex (char (sub_mono s) (sub_is_monic s)) truth_subobject ≈ s.
Proof.
  apply (sub_reindex_transport _ truth_subobject s one).
  apply char_pullback.
Qed.

(*
 The classification theorem: subobjects of x correspond to morphisms
 x ~> Ω, as an isomorphism of setoids.  Forward: char, respecting the
 SubObj equivalence by char_respects.  Backward: pullback of truth along
 h via sub_reindex, respecting ≈ of morphisms by sub_reindex_respects_mor.
 The two round trips are the lemmas above.  Ends in Defined so the
 correspondence computes. 

 --------
 分类定理：x 的子对象对应于 x ~> Ω 的态射，作为集类的同构。正向：特征，遵守 char_respects 的 SubObj 等价。反向：通过 sub_reindex 沿 h 拉回真值，遵守 sub_reindex_respects_mor 的态射 ≈。上述引理就是两次往返。以 Defined 结束，因此该对应可计算。
*)
Theorem classifier_classifies (x : C) :
  @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}.
Proof using Type HP.
  unshelve econstructor.
  - (* to: classify a subobject by its characteristic morphism / 将一个子对象根据其特征态射进行分类 *)
    simpl.
    unshelve refine {| morphism := fun s : SubObj x =>
                         char (sub_mono s) (sub_is_monic s) |}.
    (* respects the SubObj equivalence / 尊重 SubObj 等价性 *)
    intros s s' Hs.
    destruct s, s'.
    now apply char_respects.
  - (* from: pull truth back along h / 从：沿 h 拉回真相 *)
    simpl.
    unshelve refine {| morphism := fun h : x ~> Ω =>
                         sub_reindex h truth_subobject |}.
    (* the HasPullbacks instance hole left by refine / 由 refine 留下的 HasPullbacks 实例空缺 *)
    1: typeclasses eauto.
    (* respects ≈ of characteristic morphisms / 特征态射的极限 ≈ *)
    intros h h' Hh.
    now apply sub_reindex_respects_mor.
  - (* to ∘ from ≈ id, pointwise / 到 ∘ 从 ≈ 恒等映射，逐点 *)
    intro h; simpl.
    apply classifier_char_roundtrip.
  - (* from ∘ to ≈ id, pointwise / 从 ∘ 到 ≈ id，逐点 *)
    intro s; simpl.
    apply classifier_pullback_roundtrip.
Defined.

End SubobjectClassifier.
