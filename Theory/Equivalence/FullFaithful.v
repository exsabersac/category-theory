Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   The classical characterization of equivalences: a functor F : C ⟶ D is an
   equivalence of categories exactly when it is full, faithful, and
   essentially surjective.  Both directions are constructive here, because
   the library's [Full] and [EssentiallySurjective] are the split,
   choice-carrying classes ([prefmap] is a chosen section of [fmap[F]];
   [eso_obj]/[eso_iso] a chosen preimage object with its witnessing
   isomorphism), so no choice principle is consumed: the quasi-inverse is
   assembled directly from the carried data.

   Forward direction ([FF_ESO_Equivalence]): the quasi-inverse
   [ff_eso_inverse] acts by [eso_obj] on objects, and on morphisms by
   conjugating with the [eso_iso] isomorphisms and then choosing a preimage
   with [prefmap].  [prefmap] carries no functoriality nor respectfulness of
   its own (see the issue #118 note in Theory/Functor.v), so every law of
   [ff_eso_inverse] is instead recovered from faithfulness: apply
   [fmap_inj], push [fmap[F]] through with [fmap_sur], and conclude among
   the images in D.  The counit of the resulting equivalence is literally
   the family [eso_iso]; the unit component at x is the [prefmap]-image of
   [eso_iso (F x)], inverted ([ff_eso_unit_iso]).

   Converse direction, given [E : EquivalenceOfCategories F]:

   - [Equivalence_Faithful]: injectivity of [fmap[F]] is read off the
     conjugation coherence of the unit cell ([`2 equivalence_unit]).
   - [Equivalence_Inverse_Faithful]: the same statement for the
     quasi-inverse, obtained through [EquivalenceOfCategories_sym] — which
     is exactly reading it off the counit cell.
   - [Equivalence_Full]: the chosen preimage of g : F x ~> F y is the
     unit-conjugate of [fmap[quasi_inverse] g] ([equivalence_prefmap]).
     The section law is the classical argument: the F-image of the
     preimage and g itself have the same image under the faithful
     [quasi_inverse], by naturality of the unit and cancellation of its
     componentwise isomorphisms ([iso_from_monic]/[iso_to_epic] from
     Theory/Isomorphism.v).
   - [Equivalence_EssSurj]: the preimage object of d is
     [quasi_inverse d], witnessed by the counit component
     [equivalence_counit_at d].

   Transparency: [FF_ESO_Equivalence], [Equivalence_Full] and
   [Equivalence_EssSurj] end in [Defined], because their content is data (a
   functor, a chosen section, a chosen preimage object), and downstream
   developments — Theory/Equivalence/Adjoint.v builds the adjunction of an
   adjoint equivalence directly from the [prefmap]/[eso_iso] data extracted
   here — need those components to reduce.  [Equivalence_Faithful] is pure
   proof and ends in [Qed].

   Following Theory/Equivalence.v, nothing in this file is registered for
   instance resolution: quasi-inverses, chosen sections and chosen preimage
   objects are choices, always passed explicitly at use sites.

--------
nLab：https://ncatlab.org/nlab/show/equivalence+of+categories
维基百科：https://en.wikipedia.org/wiki/Equivalence_of_categories

等价的经典刻画：函子 F : C ⟶ D 当且仅当它是满的、忠实的，并且本质上是满射的，才是范畴的等价。在这里两个方向都是构造性的，因为库中的 [Full] 和 [EssentiallySurjective] 是拆分的、携带选择的类（[prefmap] 是 [fmap[F] 的一个选定截面；[eso_obj]/[eso_iso] 是一个选定的原像对象及其见证的同构），因此没有消耗选择公理：准逆函数是直接从携带的数据组装的。

前向方向 ([FF_ESO_Equivalence])：准逆
   [ff_eso_inverse] 通过 [eso_obj] 作用于对象，并且在态射上通过
   与 [eso_iso] 同构进行共轭然后选择一个 [prefmap] 的原像来作用。[prefmap] 本身没有函子性或自有的尊重性（参见 Theory/Functor.v 中的 issue #118 注释），因此 [ff_eso_inverse] 的每条定律都是通过忠实性恢复的：应用
   [fmap_inj]，将 [fmap[F]] 借助 [fmap_sur] 推过去，然后在 D 的像中得出结论。由此得到的等价的余单位实际上是 [eso_iso] 族；x 点的单位分量是 [eso_iso (F x)] 的 [prefmap] 像，取反 ([ff_eso_unit_iso])。

相反方向，给定 [E : EquivalenceOfCategories F]：

- [Equivalence_Faithful]：[fmap[F] 的单射性可以从单位单元的共轭相干性 ([`2 equivalence_unit]) 中读出。
- [Equivalence_Inverse_Faithful]：通过 [EquivalenceOfCategories_sym] 得到的准逆元的相同陈述——这正是从余单位单元中读取它。
- [Equivalence_Full]：g : F x ~> F y 的所选原像是 [fmap[quasi_inverse] g 的单位共轭 ([equivalence_prefmap])。
  截面定律是经典论证：原像的 F 映射与 g 本身在忠实的 [quasi_inverse] 下具有相同的像，这得益于单位的自然性以及其分量同构的消去 (Theory/Isomorphism.v 中的 [iso_from_monic]/[iso_to_epic])。
- [Equivalence_EssSurj]：d 的原像对象是 [quasi_inverse d]，由余单位分量 [equivalence_counit_at d] 见证。

透明性：[FF_ESO_Equivalence]、[Equivalence_Full] 和 [Equivalence_EssSurj] 终止于 [Defined]，因为它们的内容是数据（一个函子、一个选择的截面、一个选择的原像对象），而下游开发——Theory/Equivalence/Adjoint.v 直接从这里提取的 [prefmap]/[eso_iso] 数据构建伴随等价的伴随——需要这些组件来进行化简。[Equivalence_Faithful] 是纯证明，并终止于 [Qed]。

根据 Theory/Equivalence.v，本文件中没有任何内容被注册用于实例解析：准逆、选定的截面以及选定的原像对象都是选择项，总是在使用时显式传递。
*)

(*
The quasi-inverse assembled from a full, faithful, essentially
   surjective functor.  On objects it is the chosen preimage [eso_obj]; on
   morphisms it conjugates through the witnessing isomorphisms and takes
   the chosen [fmap]-preimage.

--------
由一个完全、忠实、本质上满的函子组装的拟逆。在对象上，它是选定的原像 [eso_obj]；在态射上，它通过见证同构进行共轭，并取选定的 [fmap]-原像。
*)
Program Definition ff_eso_inverse `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  D ⟶ C := {|
  fobj := eso_obj;
  fmap := fun d d' g => prefmap (from (eso_iso d') ∘ g ∘ to (eso_iso d))
|}.
Next Obligation.
  (* respectfulness of the morphism action, recovered from faithfulness / 从忠诚性恢复出的态射作用的尊重性 *)
  proper.
  apply fmap_inj.
  rewrite !fmap_sur.
  now rewrites.
Qed.
Next Obligation.
  (* preservation of identities / 恒等的保留 *)
  apply fmap_inj.
  rewrite fmap_sur, fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  (* preservation of composition: the middle [to ∘ from] pair cancels / 组合的保留：中间的 [to ∘ from] 对被抵消 *)
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (to (eso_iso _)) (from (eso_iso _))).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(*
The unit component at x : C, an isomorphism x ≅ eso_obj (F x).  Its two
   sides are the [prefmap]-images of the two sides of [eso_iso (F x)]; the
   inverse laws again go through [fmap_inj]/[fmap_sur].

--------
在 x : C 处的单位组件是一个同构 x ≅ eso_obj (F x)。它的两边是 [prefmap] 对 [eso_iso (F x)] 两边的映射；逆律同样通过 [fmap_inj]/[fmap_sur]。
*)
Program Definition ff_eso_unit_iso `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F}
  (x : C) : x ≅ eso_obj (F x) := {|
  to   := prefmap (from (eso_iso (F x)));
  from := prefmap (to (eso_iso (F x)))
|}.
Next Obligation.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  apply iso_from_to.
Qed.
Next Obligation.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  apply iso_to_from.
Qed.

(*
The counit cell F ◯ ff_eso_inverse F ≈ Id[D].  Its isomorphism family
   is literally [eso_iso]; the conjugation coherence is exactly the
   section law [fmap_sur].

--------
余单位单元 F ◯ ff_eso_inverse F ≈ Id[D]。它的同构族字面上是 [eso_iso]；共轭一致性正好是截面律 [fmap_sur]。
*)
Definition ff_eso_counit `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  F ◯ ff_eso_inverse F ≈ Id[D].
Proof.
  exists (fun d => eso_iso d).
  intros d d' g.
  exact (fmap_sur (from (eso_iso d') ∘ g ∘ to (eso_iso d))).
Defined.

(*
Conjugation coherence of the unit cell, as a standalone (opaque) lemma:
   only the two [eso_iso (F −)] pairs cancel after pushing [fmap[F]]
   through with [fmap_sur].

--------
单位胞的结合连贯性，作为独立（不透明）引理：仅在通过 [fmap_sur] 推动 [fmap[F] 后，两个 [eso_iso (F −)] 对才能抵消。
*)
Lemma ff_eso_unit_coherence `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F}
  {x y : C} (f : x ~> y) :
  f ≈ from (ff_eso_unit_iso F y)
        ∘ fmap[ff_eso_inverse F ◯ F] f
        ∘ to (ff_eso_unit_iso F x).
Proof.
  apply fmap_inj.
  simpl.
  rewrite !fmap_comp, !fmap_sur.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* The unit cell Id[C] ≈ ff_eso_inverse F ◯ F. / 晶胞 Id[C] ≈ ff_eso_inverse F ◯ F。 *)
Definition ff_eso_unit `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  Id[C] ≈ ff_eso_inverse F ◯ F.
Proof.
  exists (fun x => ff_eso_unit_iso F x).
  intros x y f.
  exact (ff_eso_unit_coherence F f).
Defined.

(*
The forward direction of the characterization: full + faithful +
   essentially surjective functors are equivalences of categories.

--------
刻画的正向方向：完全且忠实且本质上满射的函子是范畴的等价。
*)
Theorem FF_ESO_Equivalence `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  EquivalenceOfCategories F.
Proof.
  exact (@Build_EquivalenceOfCategories C D F (ff_eso_inverse F)
           (ff_eso_counit F) (ff_eso_unit F)).
Defined.

(*
The converse direction: every equivalence of categories is faithful,
   full, and essentially surjective.

--------
相反方向：每个范畴的等价都是忠实的、满射的，并且本质上是满的。
*)

Theorem Equivalence_Faithful `(E : @EquivalenceOfCategories C D F) :
  Faithful F.
Proof.
  constructor.
  intros x y f g Hfg.
  pose proof (`2 equivalence_unit x y f) as Hf; simpl in Hf.
  pose proof (`2 equivalence_unit x y g) as Hg; simpl in Hg.
  rewrite Hf, Hg.
  now rewrite Hfg.
Qed.

(*
The quasi-inverse is likewise faithful: apply the same argument to the
   symmetric equivalence, i.e. read it off the counit cell.

--------
拟逆同样是忠实的：将相同的论证应用于对称等价，即从余单位单元中直接读取它。
*)
Corollary Equivalence_Inverse_Faithful
  `(E : @EquivalenceOfCategories C D F) :
  Faithful (@quasi_inverse C D F E).
Proof.
  exact (Equivalence_Faithful (@EquivalenceOfCategories_sym C D F E)).
Qed.

(*
The chosen preimage of g : F x ~> F y under [fmap[F]]: conjugate
   [fmap[quasi_inverse] g] with the unit components.

--------
g : F x ~> F y 在 [fmap[F] 下所选择的原像：与单位分量共轭的 [fmap[quasi_inverse] g]。
*)
Definition equivalence_prefmap `(E : @EquivalenceOfCategories C D F)
  {x y : C} (g : F x ~> F y) : x ~> y :=
  from (equivalence_unit_at y)
    ∘ fmap[@quasi_inverse C D F E] g
    ∘ to (equivalence_unit_at x).

(*
The section law: [fmap[F] (equivalence_prefmap E g)] and g have the
   same image under the faithful [quasi_inverse] — by the unit's
   conjugation coherence, after cancelling the monic [from] and epic [to]
   components of the unit isomorphism.

--------
该部分定律：[fmap[F]（equivalence_prefmap E g）] 和 g 在忠实的 [quasi_inverse] 下具有相同的像——根据单位的共轭一致性，在消去单位同构的单射 [from] 和满射 [to] 分量之后。
*)
Lemma equivalence_prefmap_sur `(E : @EquivalenceOfCategories C D F)
  {x y : C} (g : F x ~> F y) :
  fmap[F] (equivalence_prefmap E g) ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  symmetry.
  apply (monic (Monic := iso_from_monic (equivalence_unit_at y))).
  apply (epic (Epic := iso_to_epic (equivalence_unit_at x))).
  exact (`2 equivalence_unit x y (equivalence_prefmap E g)).
Qed.

Theorem Equivalence_Full `(E : @EquivalenceOfCategories C D F) : Full F.
Proof.
  exact (@Build_Full C D F
           (fun x y g => equivalence_prefmap E g)
           (fun x y g => equivalence_prefmap_sur E g)).
Defined.

Theorem Equivalence_EssSurj `(E : @EquivalenceOfCategories C D F) :
  EssentiallySurjective F.
Proof.
  exact (@Build_EssentiallySurjective C D F
           (fun d => quasi_inverse d)
           (fun d => equivalence_counit_at d)).
Defined.
