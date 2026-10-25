Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(*
Pullbacks transport along an equivalence of categories.

   nLab:      https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   Theory/Equivalence/Terminal.v carries [Terminal_transport] and
   [Initial_transport], their two object readbacks and four lower-case helpers,
   and nothing else of this NAME shape.  MEASURED, with the five files of this
   change excluded (this one, the three Structure/Topos/ files and the probe): a
   whole-tree search for [Terminal_transport], [Cartesian_transport],
   [HasEqualizers_transport], [HasPullbacks_transport], [Initial_transport] or
   [Cocartesian_transport] returns 8 lines, ALL in
   Theory/Equivalence/Terminal.v, naming [Terminal_transport],
   [Initial_transport], [Terminal_transport_obj] and [Initial_transport_obj];
   the case-sensitive search does not reach [terminal_transport_unique],
   [terminal_transport_arrow], [initial_transport_unique] or
   [initial_transport_arrow], and none of those eight is a transport of a binary
   universal property.  Read it as a NAME search: other structures ARE carried
   across an equivalence under other names -- Instance/Proset/Limit.v's
   [Complete_equivalence_invariant] and [Cocomplete_equivalence_invariant],
   Theory/Equivalence/Monoidal.v's [Transported_Monoidal] and
   Theory/Equivalence/Adjunction.v's [Transported_Adjunction] -- so what is new
   here is the pullback case, not the pattern.  This is the
   binary-universal-property companion, built to the same recipe -- take the
   quasi-inverse image of the data, use the structure downstairs, push the
   answer back with F -- and, like it, with no limit machinery anywhere: no
   [Cone], no [Limit], no RAPL.

   WHY THAT MATTERS BEYOND ECONOMY.  The [Limit]-shaped route is not merely more
   expensive here, it is STRICTLY WEAKER, and the measurement is pinned in
   Test/ProbeToposColimits405.v: [Terminal_Limit] (Structure/Limit/Terminal.v)
   and [Cartesian_Limit] (Structure/Limit/Cartesian.v) are stated over
   [Category@{u Set Set}] -- they pin the ambient category's hom AND proof
   universes to the literal [Set] -- while nothing in this file pins any
   universe to [Set].  Read off BOTH binder and block, every constant here is
   over [C : Category@{u u0 u0}] -- hom identified with proof in the BINDER,
   inherited from [IsPullback] and [HasPullbacks], each refused alone at hom and
   proof levels declared strictly apart with the hom-set and the identity
   accepted, pinned in the probe -- and five of the six carry the block equation
   [u0 = u2] identifying the two categories' hom levels, while
   [is_pullback_jointly_monic]'s block is LITERALLY EMPTY over that same binder:
   the binder/block trap in miniature.

   THE HONEST CORE is [IsPullback_transport], which is apex-pinned: a
   pullback IN C of the quasi-inverse image of a cospan of D is, after
   applying F and correcting both legs by the counit isomorphisms, a
   pullback IN D of the original cospan.  [HasPullbacks_transport] merely
   chooses the pullback downstairs and packages the record.

   WHAT THE PROOF SPENDS.  Existence needs only naturality of the COUNIT
   ([equivalence_counit_to_natural]) and its invertibility.  Uniqueness needs,
   in addition, naturality of the UNIT in its conjugated form
   ([equivalence_unit_conjugate]), invertibility of both cells, and faithfulness
   of the quasi-inverse ([Equivalence_Inverse_Faithful]).  NO triangle identity
   is used -- an [EquivalenceOfCategories] carries two natural isomorphisms and
   no coherence between them, so no such identity is available, and the argument
   is arranged to avoid needing one.

   NOT DELIVERED: no statement that F PRESERVES pullbacks (an
   [IsPullback f g P p1 p2] in C carried to one in D at the F-images of
   f and g); no equalizer, product or general limit transport; no
   uniqueness of the transported pullback beyond what the universal
   property itself gives; and no dual (pushouts along an equivalence).

--------
沿着范畴的等价的拉回运送。

nLab：https://ncatlab.org/nlab/show/equivalence+of+categories
维基百科：https://en.wikipedia.org/wiki/Equivalence_of_categories

Theory/Equivalence/Terminal.v 包含 [Terminal_transport] 和 [Initial_transport]，它们的两个对象读取回写和四个小写辅助函数，以及除此之外没有该 NAME 形式的内容。经过测量，在排除该变更的五个文件（这个文件、三个 Structure/Topos/ 文件以及探针）后：对整个树进行搜索 [Terminal_transport]、[Cartesian_transport]、[HasEqualizers_transport]、[HasPullbacks_transport]、[Initial_transport] 或 [Cocartesian_transport] 返回 8 行，全部在 Theory/Equivalence/Terminal.v 中，分别命名为 [Terminal_transport]、[Initial_transport]、[Terminal_transport_obj] 和 [Initial_transport_obj]；区分大小写的搜索没有涉及 [terminal_transport_unique]、[terminal_transport_arrow]、[initial_transport_unique] 或 [initial_transport_arrow]，并且这八个中没有任何一个是二进制通用属性的传递。
将其作为名称搜索来读取：其他结构在其他名称下通过等价关系被携带——Instance/Proset/Limit.v 的 [Complete_equivalence_invariant] 和 [Cocomplete_equivalence_invariant]，Theory/Equivalence/Monoidal.v 的 [Transported_Monoidal]，以及 Theory/Equivalence/Adjunction.v 的 [Transported_Adjunction]——所以这里的新内容是拉回案例，而不是模式。这是二元通用性质的伴随对象，按照相同的配方构建——取数据的准逆像，使用下面的结构，通过 F 将答案推回——并且和它一样，任何地方都没有极限机制：没有 [Cone]，没有 [Limit]，没有 RAPL。

为什么这不仅仅是经济问题。[Limit] 形状的路线不仅在这里更昂贵，而且严格来说更弱，并且测量固定在 Test/ProbeToposColimits405.v 中：[Terminal_Limit]（Structure/Limit/Terminal.v）和 [Cartesian_Limit]（Structure/Limit/Cartesian.v）是基于 [Category@{u Set Set}] 声明的——它们将环境范畴的同态 AND 证明宇宙固定在字面上的 [Set]——而此文件中没有任何内容将任何宇宙固定在 [Set]。读取绑定器和块，这里的每个常量都是基于 [C : Category@{u u0 u0}]——同态在绑定器中与证明一致，从 [IsPullback] 和 [HasPullbacks] 继承，每个单独都被拒绝，在同态和证明层次上严格分开声明，接受同态集和恒等，在探针中固定——六个中有五个携带块方程 [u0 = u2]，识别两个范畴的同态层次，而 [is_pullback_jointly_monic] 的块在同一绑定器上实际上是空的：绑定器/块陷阱的缩影。

THE HONEST CORE 是 [IsPullback_transport]，它是 apex 固定的：在 C 中的拉回是 D 的共跨图的拟逆像，经过应用 F 并通过余单位同构矫正两条腿之后，是原始共跨图在 D 中的拉回。[HasPullbacks_transport] 只是选择楼下的拉回并打包记录。

证明所依赖的内容。存在性只需要 COUNIT ([equivalence_counit_to_natural]) 的自然性及其可逆性。唯一性还需要 UNIT 在其共轭形式中的自然性 ([equivalence_unit_conjugate])、两个单元格的可逆性，以及拟逆的忠实性 ([Equivalence_Inverse_Faithful])。没有使用三角恒等式——[EquivalenceOfCategories] 携带两个自然同构且它们之间没有相干性，因此无法使用这样的恒等式，论证被安排为避免需要它。

未传递：没有说明 F 保留拉回（C 中的一个 [IsPullback f g P p1 p2] 被 F 映射到 D 中 f 和 g 的 F-像的一个拉回）；没有等化器、积或一般极限的传递；传递的拉回的唯一性仅限于普遍性质本身提供的；也没有对偶（沿等价的推挤）。
*)

(** ** Joint monicity of a pullback's projections / ** 拉回投影的联合单射性 *)

(*
The standard consequence of the universal property: two maps into the
   apex agreeing after both projections are equal.  Stated separately
   because the transport's uniqueness clause consumes it in C while
   working in D.

--------
泛性质的标准结果：若两个映射到顶点，在经过两个投影后相同，则它们相等。单独陈述是因为在 C 中传输的唯一性条款会在 D 中操作时被用掉。
*)
Lemma is_pullback_jointly_monic {C : Category} {x y z : C}
      {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
      (HP : IsPullback f g P p1 p2) (Q : C) (a b : Q ~> P) :
  p1 ∘ a ≈ p1 ∘ b → p2 ∘ a ≈ p2 ∘ b → a ≈ b.
Proof.
  intros H1 H2.
  assert (Hc : f ∘ (p1 ∘ a) ≈ g ∘ (p2 ∘ a)).
  { rewrite !comp_assoc.
    now rewrite (is_pullback_commutes HP). }
  pose proof (is_pullback_ump HP Q (p1 ∘ a) (p2 ∘ a) Hc) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U); split; reflexivity.
  - apply (uniqueness U); split.
    + now symmetry.
    + now symmetry.
Qed.

Section PullbackTransport.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(* The two corrected legs of the transported square. / 被搬运的正方形的两个修正边。 *)
Definition pullback_transport_leg {d : D} {P : C}
           (p : P ~> @quasi_inverse C D F E d) : F P ~> d :=
  to (@equivalence_counit_at C D F E d) ∘ fmap[F] p.

(*
Any two maps into F P that agree after both corrected legs agree, when
   the two uncorrected legs are jointly monic downstairs.  This is the
   whole content of the uniqueness clause below.

--------
当两条未校正的腿在下方联合单射时，任何两个映射到 F P 的映射在两条校正过的腿都一致之后也一致。这就是下面唯一性条款的全部内容。
*)
Lemma pullback_transport_jointly_monic {x y : D} {P : C}
      {p1 : P ~> @quasi_inverse C D F E x}
      {p2 : P ~> @quasi_inverse C D F E y}
      (JM : ∀ (Z : C) (a b : Z ~> P),
              p1 ∘ a ≈ p1 ∘ b → p2 ∘ a ≈ p2 ∘ b → a ≈ b)
      {Q : D} (v w : Q ~> F P) :
  pullback_transport_leg p1 ∘ v ≈ pullback_transport_leg p1 ∘ w →
  pullback_transport_leg p2 ∘ v ≈ pullback_transport_leg p2 ∘ w →
  v ≈ w.
Proof.
  intros H1 H2.
  (*
Cancel the counit isomorphisms, then apply the faithful
     quasi-inverse.

--------
取消余单位同构，然后应用忠实的拟逆。
*)
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  (*
The unit at P is invertible, so it suffices to compare after
     [from (unit at P)].

--------
P 点的单位是可逆的，因此在 [from (unit at P)] 之后进行比较就足够了。
*)
  apply (monic (Monic := iso_from_monic
                  (@equivalence_unit_at C D F E P))).
  (* Reduce to the two projections downstairs. / 把它们缩到楼下的两个投影仪上。 *)
  apply JM.
  - apply (monic (Monic := iso_to_monic
                    (@equivalence_unit_at C D F E
                       (@quasi_inverse C D F E x)))).
    rewrite !comp_assoc.
    rewrite <- !(equivalence_unit_conjugate p1).
    rewrite <- !fmap_comp.
    apply fmap_respects.
    unfold pullback_transport_leg in H1.
    apply (monic (Monic := iso_to_monic
                    (@equivalence_counit_at C D F E x))).
    rewrite !comp_assoc.
    exact H1.
  - apply (monic (Monic := iso_to_monic
                    (@equivalence_unit_at C D F E
                       (@quasi_inverse C D F E y)))).
    rewrite !comp_assoc.
    rewrite <- !(equivalence_unit_conjugate p2).
    rewrite <- !fmap_comp.
    apply fmap_respects.
    unfold pullback_transport_leg in H2.
    apply (monic (Monic := iso_to_monic
                    (@equivalence_counit_at C D F E y))).
    rewrite !comp_assoc.
    exact H2.
Qed.

(** ** The apex-pinned transport / ** 顶点固定运输 *)

Lemma IsPullback_transport {x y z : D} {f : x ~> z} {g : y ~> z}
      {P : C}
      {p1 : P ~> @quasi_inverse C D F E x}
      {p2 : P ~> @quasi_inverse C D F E y}
      (HP : IsPullback (fmap[@quasi_inverse C D F E] f)
                       (fmap[@quasi_inverse C D F E] g) P p1 p2) :
  IsPullback f g (F P)
    (pullback_transport_leg p1) (pullback_transport_leg p2).
Proof.
  constructor.
  - (* the corrected square commutes: counit naturality on both sides / 修正的平方是可换的：两边的余单位自然性 *)
    unfold pullback_transport_leg.
    rewrite !comp_assoc.
    rewrite <- (equivalence_counit_to_natural f).
    rewrite <- (equivalence_counit_to_natural g).
    rewrite <- !comp_assoc, <- !fmap_comp.
    apply compose_respects; [reflexivity|].
    apply fmap_respects.
    exact (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    (* transport the competing cone into C with the quasi-inverse / 使用拟逆将竞争锥运输到 C *)
    assert (Hq' : fmap[@quasi_inverse C D F E] f
                    ∘ fmap[@quasi_inverse C D F E] q1
                  ≈ fmap[@quasi_inverse C D F E] g
                    ∘ fmap[@quasi_inverse C D F E] q2).
    { rewrite <- !fmap_comp.
      now apply fmap_respects. }
    destruct (is_pullback_ump HP (@quasi_inverse C D F E Q)
                (fmap[@quasi_inverse C D F E] q1)
                (fmap[@quasi_inverse C D F E] q2) Hq') as [u [U1 U2] Uu].
    unshelve refine {| unique_obj :=
      fmap[F] u ∘ from (@equivalence_counit_at C D F E Q) |}.
    + split; unfold pullback_transport_leg.
      * rewrite <- !comp_assoc, (comp_assoc (fmap[F] p1)), <- fmap_comp.
        rewrite U1, comp_assoc.
        rewrite (equivalence_counit_to_natural q1).
        rewrite <- comp_assoc, iso_to_from.
        apply id_right.
      * rewrite <- !comp_assoc, (comp_assoc (fmap[F] p2)), <- fmap_comp.
        rewrite U2, comp_assoc.
        rewrite (equivalence_counit_to_natural q2).
        rewrite <- comp_assoc, iso_to_from.
        apply id_right.
    + intros v [V1 V2].
      apply (pullback_transport_jointly_monic
               (is_pullback_jointly_monic HP)).
      * rewrite V1.
        unfold pullback_transport_leg.
        rewrite <- !comp_assoc, (comp_assoc (fmap[F] p1)), <- fmap_comp.
        rewrite U1, comp_assoc.
        rewrite (equivalence_counit_to_natural q1).
        rewrite <- comp_assoc, iso_to_from.
        now rewrite id_right.
      * rewrite V2.
        unfold pullback_transport_leg.
        rewrite <- !comp_assoc, (comp_assoc (fmap[F] p2)), <- fmap_comp.
        rewrite U2, comp_assoc.
        rewrite (equivalence_counit_to_natural q2).
        rewrite <- comp_assoc, iso_to_from.
        now rewrite id_right.
Qed.

(** ** The packaged transport / ** 包装运输 *)

Definition HasPullbacks_transport (HP : @HasPullbacks C) :
  @HasPullbacks D :=
  {| pullback := fun x y z f g =>
       is_pullback_pullback
         (IsPullback_transport
            (pullback_is_pullback _ _
               (@pullback C HP _ _ _
                  (fmap[@quasi_inverse C D F E] f)
                  (fmap[@quasi_inverse C D F E] g)))) |}.

(*
The transported pullback object is the image of the one chosen
   downstairs, on the nose.

--------
被运送的回拉对象正是楼下选择的那个对象的映像，准确无误。
*)
Example HasPullbacks_transport_obj (HP : @HasPullbacks C)
        {x y z : D} (f : x ~> z) (g : y ~> z) :
  Pull f g (@pullback D (HasPullbacks_transport HP) x y z f g)
    = F (Pull _ _ (@pullback C HP _ _ _
                     (fmap[@quasi_inverse C D F E] f)
                     (fmap[@quasi_inverse C D F E] g)))
  := eq_refl.

End PullbackTransport.
