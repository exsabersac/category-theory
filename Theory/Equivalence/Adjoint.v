Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   An adjoint equivalence is an adjunction whose unit and counit are
   componentwise isomorphisms.  The class below packages a hom-setoid
   adjunction F ⊣ U (Theory/Adjunction.v) together with, for every object,
   an [IsIsomorphism] witness for the unit component and for the counit
   component — the predicate form of Theory/Isomorphism.v, carrying a
   chosen [two_sided_inverse] and its two inverse laws about that specific
   morphism.

   The main theorem [Equivalence_to_AdjointEquivalence] refines any
   equivalence of categories (Theory/Equivalence.v) into an adjoint
   equivalence carried by the same functor and the same quasi-inverse.
   The route is direct — it does not rectify one of the two comparison
   cells through the triangle identities.  From E : EquivalenceOfCategories
   F we take the fullness, faithfulness and essential surjectivity of F
   (Theory/Equivalence/FullFaithful.v) and build the transposing hom-setoid
   isomorphism outright:

     to   f := prefmap (from (eso_iso d) ∘ f)      ([equiv_adj_to])
     from g := to (eso_iso d) ∘ fmap[F] g          ([equiv_adj_from])

   For the instances extracted from E, [prefmap] is [equivalence_prefmap E]
   and [eso_iso d] is [equivalence_counit_at d], both definitionally
   (because [Equivalence_Full] and [Equivalence_EssSurj] end in [Defined]),
   so the two transposes are stated in that vocabulary.  [prefmap] carries
   no respectfulness of its own (the issue #118 note in Theory/Functor.v);
   every law below is instead recovered from faithfulness: apply
   [fmap_inj], push [fmap[F]] through with [equivalence_prefmap_sur], and
   conclude among the images in D.  Naturality in the target argument is
   the conjugation coherence of the counit cell ([fun_equiv_fmap_from]
   applied to [equivalence_counit]).  The unit and counit of the resulting
   adjunction are isomorphisms by construction: the F-image of the unit is
   an inverse counit-cell component ([equiv_adjunction_fmap_unit]) and the
   counit is a counit-cell component on the nose
   ([equiv_adjunction_counit_at]).

   Conversely, [AdjointEquivalence_to_Equivalence] reads an equivalence of
   categories off an adjoint equivalence: the two cells are the pointwise
   [IsIsoToIso] isomorphisms, and their conjugation coherence is the
   naturality of the unit and counit — [adj_unit_naturality] and
   [adj_counit_naturality] below, the arbitrary-morphism generalizations
   of [unit_comp] and [counit_comp] from Theory/Adjunction.v.  Composing
   the two directions through [EquivalenceOfCategories_sym] exchanges the
   two sides: [AdjointEquivalence_swap] turns an adjoint equivalence
   between F and U into one between U and F, whose underlying adjunction
   [AdjointEquivalence_swap_adjunction] is the swapped U ⊣ F.

   Following Theory/Equivalence.v, nothing in this file is registered for
   instance resolution: an adjoint equivalence is a choice of data, always
   passed explicitly at use sites.

--------
nLab：https://ncatlab.org/nlab/show/adjoint+equivalence
维基百科：https://en.wikipedia.org/wiki/Equivalence_of_categories

伴随等价是一个伴随，其单位和余单位在各分量上都是同构。下面的类封装了一个同态集合伴随 F ⊣ U (Theory/Adjunction.v)，并且对于每个对象，提供了单位分量和余单位分量的 [IsIsomorphism] 见证——这是 Theory/Isomorphism.v 的谓词形式，携带一个特定的 [two_sided_inverse] 及其关于该特定态射的两个逆律。

主定理 [Equivalence_to_AdjointEquivalence] 将任意的范畴等价 (Theory/Equivalence.v) 精炼为一个由同一个函子和同一个准逆函子承载的伴随等价。方法是直接的——它不会通过三角恒等式来修正两个比较单元中的任何一个。对于 E : EquivalenceOfCategories F，我们取 F 的满性、忠实性和本质上满射性 (Theory/Equivalence/FullFaithful.v)，并直接构建置换 hom-集合同态的同构:

to   f := prefmap (from (eso_iso d) ∘ f)      ([equiv_adj_to])
     from g := to (eso_iso d) ∘ fmap[F] g          ([equiv_adj_from])

对于从 E 中提取的实例，[prefmap] 是 [equivalence_prefmap E]，[eso_iso d] 是 [equivalence_counit_at d]，两者都是定义上的（因为 [Equivalence_Full] 和 [Equivalence_EssSurj] 以 [Defined] 结尾），因此这两个转置在该词汇中被陈述。[prefmap] 本身不带有任何尊重性（Theory/Functor.v 中的问题 #118 注释）；下面的每条定律都是通过忠实性恢复的：应用 [fmap_inj]，通过 [equivalence_prefmap_sur] 推动 [fmap[F]，并在 D 中的像之间得出结论。目标参数中的自然性是余单位单元的共轭相容性（对 [equivalence_counit] 应用 [fun_equiv_fmap_from]）。由此得到的伴随的单位和余单位在构造上都是同构：单位的 F-像是余单位单元的逆分量（[equiv_adjunction_fmap_unit]），余单位则是一个精确的余单位单元分量（[equiv_adjunction_counit_at]）。

相反，[AdjointEquivalence_to_Equivalence] 从伴随等价中读取了范畴的等价：两个单元是逐点的 [IsIsoToIso] 同构，它们的共轭相干性是单位和余单位的自然性——见下文的 [adj_unit_naturality] 和 [adj_counit_naturality]，这是对 Theory/Adjunction.v 中 [unit_comp] 和 [counit_comp] 的任意态射推广。通过 [EquivalenceOfCategories_sym] 组合两个方向会交换两边：[AdjointEquivalence_swap] 将 F 和 U 之间的伴随等价转换为 U 和 F 之间的伴随等价，其基础伴随关系 [AdjointEquivalence_swap_adjunction] 是交换后的 U ⊣ F。

根据 Theory/Equivalence.v，本文件中没有内容被注册用于实例解析：伴随等价是一种数据选择，总是在使用处显式传递。
*)

(*
An adjoint equivalence: an adjunction both of whose comparison
   transformations are componentwise invertible.  The two extra fields are
   [IsIsomorphism] witnesses about the derived [unit] and [counit] of the
   underlying hom-setoid adjunction.

--------
伴随等价：一个伴随，其比较变换的每个分量都是可逆的。这两个额外的字段是关于底层同态集合伴随的派生 [unit] 和 [counit] 的 [IsIsomorphism] 证明。
*)
Class AdjointEquivalence {C D : Category} (F : C ⟶ D) (U : D ⟶ C) := {
  adj_equivalence : F ⊣ U;
  adj_equiv_unit_iso (x : C) :
    IsIsomorphism (@unit _ _ _ _ adj_equivalence x);
  adj_equiv_counit_iso (y : D) :
    IsIsomorphism (@counit _ _ _ _ adj_equivalence y)
}.

(*
Naturality of the unit and counit of a hom-setoid adjunction, at an
   arbitrary morphism.  Theory/Adjunction.v proves these squares only in
   the shapes needed there — [unit_comp] pins the codomain to a U-image
   and [counit_comp] pins the domain to an F-image — but the rewriting
   argument is insensitive to that, so we restate them generally.  The
   variable convention follows Theory/Adjunction.v: F : D ⟶ C is the left
   adjoint and U : C ⟶ D the right adjoint.

--------
在任意态射下，同构集配对伴随的单位元和余单位元的自然性。《Theory/Adjunction.v》仅在那里所需的形状下证明了这些交换图——[unit_comp] 将余域固定为 U 的像，[counit_comp] 将定义域固定为 F 的像——但重写论证对这些不敏感，因此我们将它们一般性地重述。变量约定遵循《Theory/Adjunction.v》：F : D ⟶ C 是左伴随，U : C ⟶ D 是右伴随。
*)

Lemma adj_unit_naturality {C D : Category} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) {x y : D} (f : x ~{D}~> y) :
  fmap[U] (fmap[F] f) ∘ @unit C D F U A x ≈ @unit C D F U A y ∘ f.
Proof.
  unfold unit.
  rewrite <- to_adj_nat_r.
  rewrite <- to_adj_nat_l.
  now rewrite id_left, id_right.
Qed.

Lemma adj_counit_naturality {C D : Category} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) {x y : C} (f : x ~{C}~> y) :
  @counit C D F U A y ∘ fmap[F] (fmap[U] f) ≈ f ∘ @counit C D F U A x.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  now rewrite id_left, id_right.
Qed.

(* ** From an equivalence of categories to an adjoint equivalence / ** 从范畴等价到伴随等价 *)

(*
The forward transpose: f : F x ~> d goes to the chosen fmap-preimage of
   its conjugate under the inverse counit-cell component at d.

--------
前向转置：f : F x ~> d 变为其在 d 的逆余元单元分量下共轭的选定 fmap-原像。
*)
Definition equiv_adj_to `(E : @EquivalenceOfCategories C D F)
  {x : C} {d : D} (f : F x ~{D}~> d) :
  x ~{C}~> @quasi_inverse C D F E d :=
  equivalence_prefmap E (from (equivalence_counit_at d) ∘ f).

(*
The inverse transpose: g : x ~> quasi_inverse d returns to D through F
   and closes with the forward counit-cell component at d.

--------
逆转置：g : x ~> quasi_inverse d 通过 F 返回到 D，并通过 d 的前向余单位单元分量闭合。
*)
Definition equiv_adj_from `(E : @EquivalenceOfCategories C D F)
  {x : C} {d : D} (g : x ~{C}~> @quasi_inverse C D F E d) :
  F x ~{D}~> d :=
  to (equivalence_counit_at d) ∘ fmap[F] g.

(*
Respectfulness of the forward transpose.  [equivalence_prefmap] is not
   assumed respectful; injectivity of [fmap[F]] recovers it.

--------
前向转置的尊重性。[equivalence_prefmap] 不被假定为尊重性；[fmap[F] 的单射性恢复了它。
*)
Lemma equiv_adj_to_respects `(E : @EquivalenceOfCategories C D F)
  (x : C) (d : D) :
  Proper (equiv ==> equiv) (@equiv_adj_to C D F E x d).
Proof.
  intros f g Hfg.
  apply (fmap_inj (Faithful := Equivalence_Faithful E)).
  unfold equiv_adj_to.
  rewrite !equivalence_prefmap_sur.
  now rewrite Hfg.
Qed.

(* The inverse transpose is respectful because [fmap] and composition are. / 逆转置是尊重的，因为 [fmap] 和组合是尊重的。 *)
Lemma equiv_adj_from_respects `(E : @EquivalenceOfCategories C D F)
  (x : C) (d : D) :
  Proper (equiv ==> equiv) (@equiv_adj_from C D F E x d).
Proof.
  intros f g Hfg.
  unfold equiv_adj_from.
  now rewrite Hfg.
Qed.

(*
The transposes are mutually inverse: reduce to images by faithfulness,
   then cancel the counit-cell isomorphism.

--------
转置是互为逆的：通过忠实性化为像，然后消去余单元-单元同构。
*)
Lemma equiv_adj_to_from `(E : @EquivalenceOfCategories C D F)
  {x : C} {d : D} (g : x ~{C}~> @quasi_inverse C D F E d) :
  equiv_adj_to E (equiv_adj_from E g) ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Faithful E)).
  unfold equiv_adj_to, equiv_adj_from.
  rewrite equivalence_prefmap_sur.
  rewrite comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Lemma equiv_adj_from_to `(E : @EquivalenceOfCategories C D F)
  {x : C} {d : D} (f : F x ~{D}~> d) :
  equiv_adj_from E (equiv_adj_to E f) ≈ f.
Proof.
  unfold equiv_adj_to, equiv_adj_from.
  rewrite equivalence_prefmap_sur.
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(*
The transposing isomorphism of hom-setoids, one Sets-isomorphism per
   pair of objects, with the transposes above as underlying maps.

--------
同态集合的换位同构，对于每对对象是一个集合同构，上述换位映射作为基础映射。
*)
Definition equiv_adj_iso `(E : @EquivalenceOfCategories C D F)
  (x : C) (d : D) :
  @Isomorphism Sets
    {| carrier := @hom D (F x) d
     ; is_setoid := @homset D (F x) d |}
    {| carrier := @hom C x (@quasi_inverse C D F E d)
     ; is_setoid := @homset C x (@quasi_inverse C D F E d) |}.
Proof.
  unshelve eapply Build_Isomorphism.
  - unshelve eapply Build_SetoidMorphism.
    + exact (@equiv_adj_to C D F E x d).
    + exact (equiv_adj_to_respects E x d).
  - unshelve eapply Build_SetoidMorphism.
    + exact (@equiv_adj_from C D F E x d).
    + exact (equiv_adj_from_respects E x d).
  - exact (@equiv_adj_to_from C D F E x d).
  - exact (@equiv_adj_from_to C D F E x d).
Defined.

(* Naturality of the forward transpose in the source argument. / 源参数中前向转置的自然性。 *)
Lemma equiv_adj_to_nat_l `(E : @EquivalenceOfCategories C D F)
  (x y : C) (z : D) (f : F y ~{D}~> z) (g : x ~{C}~> y) :
  equiv_adj_to E (f ∘ fmap[F] g) ≈ equiv_adj_to E f ∘ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Faithful E)).
  unfold equiv_adj_to.
  rewrite fmap_comp.
  rewrite !equivalence_prefmap_sur.
  now rewrite comp_assoc.
Qed.

(*
Naturality of the forward transpose in the target argument: after
   faithfulness, this is the conjugation coherence of the counit cell.

--------
目标参数中前向转置的自然性：在忠实性之后，这是余单元胞的共轭相干性。
*)
Lemma equiv_adj_to_nat_r `(E : @EquivalenceOfCategories C D F)
  (x : C) (y z : D) (f : y ~{D}~> z) (g : F x ~{D}~> y) :
  equiv_adj_to E (f ∘ g) ≈ fmap[@quasi_inverse C D F E] f ∘ equiv_adj_to E g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Faithful E)).
  unfold equiv_adj_to.
  rewrite fmap_comp.
  rewrite !equivalence_prefmap_sur.
  pose proof (fun_equiv_fmap_from
                (@equivalence_counit C D F E) y z f) as Hnat;
  simpl in Hnat.
  unfold equivalence_counit_at.
  rewrite !comp_assoc.
  now rewrite Hnat.
Qed.

(*
The adjunction F ⊣ quasi_inverse, assembled through [Build_Adjunction']
   (which derives the two inverse-transpose naturality fields from the
   forward ones).

--------
通过 [Build_Adjunction'] 组装的伴随 F ⊣ quasi_inverse（它从前向的自然性字段派生出两个逆转置自然性字段）。
*)
Definition equiv_adjunction `(E : @EquivalenceOfCategories C D F) :
  F ⊣ @quasi_inverse C D F E :=
  @Build_Adjunction' D C F (@quasi_inverse C D F E)
    (equiv_adj_iso E)
    (equiv_adj_to_nat_l E)
    (equiv_adj_to_nat_r E).

(*
The counit of [equiv_adjunction] is the counit-cell component: the
   definitional counit is [to (equivalence_counit_at d) ∘ fmap[F] id], and
   the trailing identity cancels.

--------
[equiv_adjunction] 的余单元是余单元单元组件：定义的余单元是 [to (equivalence_counit_at d) ∘ fmap[F] id，尾随的恒等式会被消去。
*)
Corollary equiv_adjunction_counit_at `(E : @EquivalenceOfCategories C D F)
  (d : D) :
  @counit _ _ _ _ (equiv_adjunction E) d ≈ to (equivalence_counit_at d).
Proof.
  transitivity (equiv_adj_from E (id[@quasi_inverse C D F E d])).
  - reflexivity.
  - unfold equiv_adj_from.
    rewrite fmap_id.
    now rewrite id_right.
Qed.

(*
The F-image of the unit of [equiv_adjunction] is the inverse
   counit-cell component at F x ([equivalence_prefmap_sur], after
   cancelling the inner identity).

--------
[equiv_adjunction] 单元的 F-像是在 F x ([equivalence_prefmap_sur]) 处的逆协单元-胞分量（在消去内部恒等元之后）。
*)
Corollary equiv_adjunction_fmap_unit `(E : @EquivalenceOfCategories C D F)
  (x : C) :
  fmap[F] (@unit _ _ _ _ (equiv_adjunction E) x)
    ≈ from (equivalence_counit_at (F x)).
Proof.
  transitivity (fmap[F] (equiv_adj_to E (id[F x]))).
  - reflexivity.
  - unfold equiv_adj_to.
    rewrite equivalence_prefmap_sur.
    now rewrite id_right.
Qed.

(*
The chosen inverse of the unit component at x: the fmap-preimage of the
   forward counit-cell component at F x.

--------
在 x 处单位分量的选定逆元：F x 处正向余单元-单元分量的 fmap-原像。
*)
Definition equiv_adjunction_unit_inv `(E : @EquivalenceOfCategories C D F)
  (x : C) : @quasi_inverse C D F E (F x) ~{C}~> x :=
  equivalence_prefmap E (to (equivalence_counit_at (F x))).

(*
The two inverse laws for the unit, both through faithfulness: the
   images compose to the two counit-cell cancellations at F x.

--------
单位的两个逆律，都通过忠诚：这些图像组合成 F x 上的两个余单位-单元消去。
*)
Lemma equiv_adjunction_unit_right_inverse
  `(E : @EquivalenceOfCategories C D F) (x : C) :
  @unit _ _ _ _ (equiv_adjunction E) x ∘ equiv_adjunction_unit_inv E x ≈ id.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Faithful E)).
  rewrite fmap_comp.
  rewrite equiv_adjunction_fmap_unit.
  unfold equiv_adjunction_unit_inv.
  rewrite equivalence_prefmap_sur.
  rewrite fmap_id.
  apply iso_from_to.
Qed.

Lemma equiv_adjunction_unit_left_inverse
  `(E : @EquivalenceOfCategories C D F) (x : C) :
  equiv_adjunction_unit_inv E x ∘ @unit _ _ _ _ (equiv_adjunction E) x ≈ id.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Faithful E)).
  rewrite fmap_comp.
  rewrite equiv_adjunction_fmap_unit.
  unfold equiv_adjunction_unit_inv.
  rewrite equivalence_prefmap_sur.
  rewrite fmap_id.
  apply iso_to_from.
Qed.

(* The unit of [equiv_adjunction] is an isomorphism. / [equiv_adjunction] 的单位是同构。 *)
Definition equiv_adjunction_unit_iso `(E : @EquivalenceOfCategories C D F)
  (x : C) : IsIsomorphism (@unit _ _ _ _ (equiv_adjunction E) x) :=
  @Build_IsIsomorphism C x (@quasi_inverse C D F E (F x))
    (@unit _ _ _ _ (equiv_adjunction E) x)
    (equiv_adjunction_unit_inv E x)
    (equiv_adjunction_unit_right_inverse E x)
    (equiv_adjunction_unit_left_inverse E x).

(*
The two inverse laws for the counit are the counit-cell cancellations
   themselves, by [equiv_adjunction_counit_at].

--------
伴随函元的两个逆律就是伴随函元单元的自我消去，由 [equiv_adjunction_counit_at] 提供。
*)
Lemma equiv_adjunction_counit_right_inverse
  `(E : @EquivalenceOfCategories C D F) (d : D) :
  @counit _ _ _ _ (equiv_adjunction E) d ∘ from (equivalence_counit_at d)
    ≈ id.
Proof.
  rewrite equiv_adjunction_counit_at.
  apply iso_to_from.
Qed.

Lemma equiv_adjunction_counit_left_inverse
  `(E : @EquivalenceOfCategories C D F) (d : D) :
  from (equivalence_counit_at d) ∘ @counit _ _ _ _ (equiv_adjunction E) d
    ≈ id.
Proof.
  rewrite equiv_adjunction_counit_at.
  apply iso_from_to.
Qed.

(* The counit of [equiv_adjunction] is an isomorphism. / [equiv_adjunction] 的余单位是一个同构。 *)
Definition equiv_adjunction_counit_iso `(E : @EquivalenceOfCategories C D F)
  (d : D) : IsIsomorphism (@counit _ _ _ _ (equiv_adjunction E) d) :=
  @Build_IsIsomorphism D (F (@quasi_inverse C D F E d)) d
    (@counit _ _ _ _ (equiv_adjunction E) d)
    (from (equivalence_counit_at d))
    (equiv_adjunction_counit_right_inverse E d)
    (equiv_adjunction_counit_left_inverse E d).

(*
The main refinement: every equivalence of categories is an adjoint
   equivalence between the same functor and its quasi-inverse.

--------
主要的改进：每一个范畴等价都是同一个函子及其拟逆的伴随等价。
*)
Theorem Equivalence_to_AdjointEquivalence
  `(E : @EquivalenceOfCategories C D F) :
  AdjointEquivalence F (@quasi_inverse C D F E).
Proof.
  exact (@Build_AdjointEquivalence C D F (@quasi_inverse C D F E)
           (equiv_adjunction E)
           (equiv_adjunction_unit_iso E)
           (equiv_adjunction_counit_iso E)).
Defined.

(* ** From an adjoint equivalence back to an equivalence of categories / ** 从伴随等价回到范畴等价 *)

(*
Conjugation coherence of the counit: the [Functor_Setoid] coherence
   condition for the counit cell, read off the counit's naturality square
   by inverting its component at the target.

--------
余单位的结合一致性：余单位单元的 [Functor_Setoid] 一致性条件，通过反转其在目标处的分量，从余单位的自然性方格中读取。
*)
Lemma adjoint_equiv_counit_coherence `(A : @AdjointEquivalence C D F U)
  {d d' : D} (g : d ~{D}~> d') :
  fmap[F] (fmap[U] g)
    ≈ @two_sided_inverse D _ _ _ (@adj_equiv_counit_iso C D F U A d')
        ∘ g
        ∘ @counit D C F U (@adj_equivalence C D F U A) d.
Proof.
  rewrite <- (id_left (fmap[F] (fmap[U] g))).
  rewrite <- (@is_left_inverse D _ _ _ (@adj_equiv_counit_iso C D F U A d')).
  rewrite <- comp_assoc.
  rewrite (adj_counit_naturality (@adj_equivalence C D F U A) g).
  now rewrite comp_assoc.
Qed.

(*
Conjugation coherence of the unit, dually: invert the unit's component
   at the target of its naturality square.

--------
单位的结合一致性，双重地：在其自然性方块的目标处反转单位的组成部分。
*)
Lemma adjoint_equiv_unit_coherence `(A : @AdjointEquivalence C D F U)
  {x y : C} (f : x ~{C}~> y) :
  f ≈ @two_sided_inverse C _ _ _ (@adj_equiv_unit_iso C D F U A y)
        ∘ fmap[U] (fmap[F] f)
        ∘ @unit D C F U (@adj_equivalence C D F U A) x.
Proof.
  rewrite <- comp_assoc.
  rewrite (adj_unit_naturality (@adj_equivalence C D F U A) f).
  rewrite comp_assoc.
  rewrite (@is_left_inverse C _ _ _ (@adj_equiv_unit_iso C D F U A y)).
  now rewrite id_left.
Qed.

(*
The counit cell F ◯ U ≈ Id[D]: componentwise the [IsIsoToIso] packaging
   of the counit isomorphisms, coherent by the lemma above.

--------
余单元元 F ◯ U ≈ Id[D]：在分量上，余单元同构的 [IsIsoToIso] 包装，由上面的引理保证一致性。
*)
Definition AdjointEquivalence_to_counit `(A : @AdjointEquivalence C D F U) :
  F ◯ U ≈ Id[D].
Proof.
  exists (fun d => @IsIsoToIso D _ _ _ (@adj_equiv_counit_iso C D F U A d)).
  intros d d' g.
  exact (adjoint_equiv_counit_coherence A g).
Defined.

(* The unit cell Id[C] ≈ U ◯ F, dually. / 晶胞 Id[C] ≈ U ◯ F，双重地。 *)
Definition AdjointEquivalence_to_unit `(A : @AdjointEquivalence C D F U) :
  Id[C] ≈ U ◯ F.
Proof.
  exists (fun x => @IsIsoToIso C _ _ _ (@adj_equiv_unit_iso C D F U A x)).
  intros x y f.
  exact (adjoint_equiv_unit_coherence A f).
Defined.

(*
An adjoint equivalence yields an equivalence of categories: the right
   adjoint serves as the quasi-inverse.

--------
伴随等价会产生范畴等价：右伴随充当拟逆。
*)
Definition AdjointEquivalence_to_Equivalence
  `(A : @AdjointEquivalence C D F U) : EquivalenceOfCategories F :=
  @Build_EquivalenceOfCategories C D F U
    (AdjointEquivalence_to_counit A)
    (AdjointEquivalence_to_unit A).

(*
Swapping the two sides: U is itself part of an adjoint equivalence with
   quasi-inverse F, obtained by symmetrizing the induced equivalence of
   categories and refining it back.

--------
交换两边：U 本身是与拟逆 F 的伴随等价的一部分，通过对诱导的范畴等价进行对称化并将其细化回去得到。
*)
Definition AdjointEquivalence_swap `(A : @AdjointEquivalence C D F U) :
  AdjointEquivalence U F :=
  Equivalence_to_AdjointEquivalence
    (@EquivalenceOfCategories_sym C D F (AdjointEquivalence_to_Equivalence A)).

(*
In particular the two adjoints trade places: the swapped adjunction
   U ⊣ F underlying [AdjointEquivalence_swap].

--------
尤其是这两个伴随交换了位置：底层于 [AdjointEquivalence_swap] 的交换伴随 U ⊣ F。
*)
Definition AdjointEquivalence_swap_adjunction
  `(A : @AdjointEquivalence C D F U) : U ⊣ F :=
  @adj_equivalence D C U F (AdjointEquivalence_swap A).
