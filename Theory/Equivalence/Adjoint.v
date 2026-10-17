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

   本文件给出伴随等价相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class AdjointEquivalence {C D : Category} (F : C ⟶ D) (U : D ⟶ C) := {
  adj_equivalence : F ⊣ U;
  adj_equiv_unit_iso (x : C) :
    IsIsomorphism (@unit _ _ _ _ adj_equivalence x);
  adj_equiv_counit_iso (y : D) :
    IsIsomorphism (@counit _ _ _ _ adj_equivalence y)
}.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* ** From an equivalence of categories to an adjoint equivalence *)

(* 相关说明。 （已译） *)
Definition equiv_adj_to `(E : @EquivalenceOfCategories C D F)
  {x : C} {d : D} (f : F x ~{D}~> d) :
  x ~{C}~> @quasi_inverse C D F E d :=
  equivalence_prefmap E (from (equivalence_counit_at d) ∘ f).

(* 相关说明。 （已译） *)
Definition equiv_adj_from `(E : @EquivalenceOfCategories C D F)
  {x : C} {d : D} (g : x ~{C}~> @quasi_inverse C D F E d) :
  F x ~{D}~> d :=
  to (equivalence_counit_at d) ∘ fmap[F] g.

(* Respectfulness of the forward transpose.  [equivalence_prefmap] is not
   assumed respectful; injectivity of [fmap[F]] recovers it. *)
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

(* The inverse transpose respectful because [fmap] 复合 are. （已译） *)
Lemma equiv_adj_from_respects `(E : @EquivalenceOfCategories C D F)
  (x : C) (d : D) :
  Proper (equiv ==> equiv) (@equiv_adj_from C D F E x d).
Proof.
  intros f g Hfg.
  unfold equiv_adj_from.
  now rewrite Hfg.
Qed.

(* The transposes mutually inverse: reduce images faithfulness,
 then cancel counit-cell 同构. （已译） *)
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

(* The transposing 同构 hom-setoids, one Sets-同构 per
 pair 对象, transposes above underlying maps. （已译） *)
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

(* Naturality forward transpose source 论元. （已译） *)
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

(* Naturality forward transpose target 论元: after
 faithfulness, 这是 conjugation coherence counit cell. （已译） *)
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

(* The 伴随 F ⊣ quasi_inverse, assembled through [Build_Adjunction']
 (which derives two inverse-transpose 自然性 fields the
 forward ones). （已译） *)
Definition equiv_adjunction `(E : @EquivalenceOfCategories C D F) :
  F ⊣ @quasi_inverse C D F E :=
  @Build_Adjunction' D C F (@quasi_inverse C D F E)
    (equiv_adj_iso E)
    (equiv_adj_to_nat_l E)
    (equiv_adj_to_nat_r E).

(* The counit [equiv_adjunction] counit-cell component: the
 definitional counit [to (等价_counit_at d) ∘ fmap[F] id], and
 trailing 恒等 cancels. （已译） *)
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

(* The F-image unit [equiv_adjunction] inverse
 counit-cell component at F x ([equivalence_prefmap_sur], after
 cancelling inner 恒等). （已译） *)
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

(* 相关说明。 （已译） *)
Definition equiv_adjunction_unit_inv `(E : @EquivalenceOfCategories C D F)
  (x : C) : @quasi_inverse C D F E (F x) ~{C}~> x :=
  equivalence_prefmap E (to (equivalence_counit_at (F x))).

(* 相关说明。 （已译） *)
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

(* The unit of [equiv_adjunction] is an isomorphism. *)
Definition equiv_adjunction_unit_iso `(E : @EquivalenceOfCategories C D F)
  (x : C) : IsIsomorphism (@unit _ _ _ _ (equiv_adjunction E) x) :=
  @Build_IsIsomorphism C x (@quasi_inverse C D F E (F x))
    (@unit _ _ _ _ (equiv_adjunction E) x)
    (equiv_adjunction_unit_inv E x)
    (equiv_adjunction_unit_right_inverse E x)
    (equiv_adjunction_unit_left_inverse E x).

(* 相关说明。 （已译） *)
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

(* The counit of [equiv_adjunction] is an isomorphism. *)
Definition equiv_adjunction_counit_iso `(E : @EquivalenceOfCategories C D F)
  (d : D) : IsIsomorphism (@counit _ _ _ _ (equiv_adjunction E) d) :=
  @Build_IsIsomorphism D (F (@quasi_inverse C D F E d)) d
    (@counit _ _ _ _ (equiv_adjunction E) d)
    (from (equivalence_counit_at d))
    (equiv_adjunction_counit_right_inverse E d)
    (equiv_adjunction_counit_left_inverse E d).

(* The main refinement: every 等价 范畴 adjoint
 等价 between same 函子 quasi-inverse. （已译） *)
Theorem Equivalence_to_AdjointEquivalence
  `(E : @EquivalenceOfCategories C D F) :
  AdjointEquivalence F (@quasi_inverse C D F E).
Proof.
  exact (@Build_AdjointEquivalence C D F (@quasi_inverse C D F E)
           (equiv_adjunction E)
           (equiv_adjunction_unit_iso E)
           (equiv_adjunction_counit_iso E)).
Defined.

(* ** From an adjoint equivalence back to an equivalence of categories *)

(* Conjugation coherence counit: [Functor_Setoid] coherence
 condition counit cell, read off counit's 自然性 square
 inverting component at target. （已译） *)
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

(* Conjugation coherence unit, dually: invert unit's component
 at target 自然性 square. （已译） *)
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

(* The counit cell F ◯ U ≈ Id[D]: componentwise [IsIsoToIso] packaging
 counit isomorphisms, coherent 引理 above. （已译） *)
Definition AdjointEquivalence_to_counit `(A : @AdjointEquivalence C D F U) :
  F ◯ U ≈ Id[D].
Proof.
  exists (fun d => @IsIsoToIso D _ _ _ (@adj_equiv_counit_iso C D F U A d)).
  intros d d' g.
  exact (adjoint_equiv_counit_coherence A g).
Defined.

(* The unit cell Id[C] ≈ U ◯ F, dually. *)
Definition AdjointEquivalence_to_unit `(A : @AdjointEquivalence C D F U) :
  Id[C] ≈ U ◯ F.
Proof.
  exists (fun x => @IsIsoToIso C _ _ _ (@adj_equiv_unit_iso C D F U A x)).
  intros x y f.
  exact (adjoint_equiv_unit_coherence A f).
Defined.

(* An adjoint 等价 yields 等价 范畴: right
 adjoint serves quasi-inverse. （已译） *)
Definition AdjointEquivalence_to_Equivalence
  `(A : @AdjointEquivalence C D F U) : EquivalenceOfCategories F :=
  @Build_EquivalenceOfCategories C D F U
    (AdjointEquivalence_to_counit A)
    (AdjointEquivalence_to_unit A).

(* Swapping two sides: U itself part adjoint 等价 with
 quasi-inverse F, obtained symmetrizing induced 等价 of
 范畴 refining it back. （已译） *)
Definition AdjointEquivalence_swap `(A : @AdjointEquivalence C D F U) :
  AdjointEquivalence U F :=
  Equivalence_to_AdjointEquivalence
    (@EquivalenceOfCategories_sym C D F (AdjointEquivalence_to_Equivalence A)).

(* In particular two adjoints trade places: swapped 伴随
 U ⊣ F underlying [AdjointEquivalence_swap]. （已译） *)
Definition AdjointEquivalence_swap_adjunction
  `(A : @AdjointEquivalence C D F U) : U ⊣ F :=
  @adj_equivalence D C U F (AdjointEquivalence_swap A).
