(*
   本文件为测试：ProbeWellPowered451。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Equalizer.Fork.
Require Import Coq.Logic.Hurkens.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.GAFT.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.WellPowered.Counterexample.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Grp.WellPowered.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Instance.FinSet.WellPowered.
Require Import Category.Adjunction.SAFT.WellPowered.
Require Import Category.Adjunction.SAFT.Sets.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Variety.Limit.
Require Import Category.Instance.Variety.Spanning.
Require Import Category.Instance.Ordinal.Large.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Structure.Equalizer.Wide.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe451_absent_name.

(** ** A. The definition, its exhaustiveness clause and the headline *)

Check (@wp_to_from : ∀ (C : Category) (x : C) (W : WellPoweredAt x)
  (u : SubObj x), wp_to W (wp_from W u) ≈ u).

Check (@wellpowered_complete_has_intersections :
  ∀ (C : Category) (WP : WellPowered C) (comp : @Complete C) (x : C)
    (P : SubObj x → Type), (∀ m m' : SubObj x, m ≈ m' → P m → P m') →
  { w : SubObj x & IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w }).

Check (@cowellpowered_cocomplete_has_cointersections :
  ∀ (C : Category) (CWP : CoWellPowered C) (cocomp : @Cocomplete C) (x : C)
    (P : QuotObj x → Type), (∀ q q' : QuotObj x, q ≈ q' → P q → P q') →
  { w : QuotObj x &
    @IsIntersection (C^op) x _ (fun k : { q : QuotObj x & P q } => `1 k) w }).

(* The dual is the definition at the opposite category, on the nose. *)
Example p451_cowp_is_wp_op (C : Category) :
  CoWellPowered C = WellPowered (C^op) := eq_refl.

(* The intersection IS the small reindexed one. *)
Example p451_intersection_is_small (C : Category) (WP : WellPowered C)
  (comp : @Complete C) (x : C) (P : SubObj x → Type)
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  `1 (wellpowered_complete_has_intersections WP comp x P HP)
    = complete_intersection comp (wp_class_family (WP x) P) := eq_refl.

(** ** N1 (UNIVERSE): the trivial witness is refused under the pin *)

(* CONTROL: the per-object record, left unpinned, takes the trivial index
   at [Sets]. *)
Definition p451_trivial_at_sets (X : Sets) : WellPoweredAt X := wp_trivial X.

(* CONTROL: a copy of [WellPowered] with the pin [w <= h] deleted accepts the
   trivial witness at [Sets], so the pin is what N1 meets. *)
Definition p451_WellPowered_unpinned@{o h w s t | o <= s, h <= s, h < t +}
  (C : Category@{o h h}) := ∀ x : C, WellPoweredAt@{w o s h t} x.

Definition p451_trivial_unpinned_sets :
  p451_WellPowered_unpinned Sets := fun X => wp_trivial X.

(* CONTROL: objects at or below the homs, and the trivial index is small. *)
Definition p451_trivial_small@{o h t | o <= h, h < t +}
  (C : Category@{o h h}) : WellPowered@{o h h h t} C := trivial_small C.

Fail Definition p451_n1_trivial_at_pin@{o so w s t} :
  WellPowered@{so o w s t} Sets@{o so} := fun X => wp_trivial X.

(** ** N2 (UNIVERSE): [Sets] one universe up is refused at the pin, and the
    [Untruncate] conditional is accepted there *)

(* CONTROL: the witness one universe up, per object. *)
Definition p451_sets_up@{o so | o < so +} (X : SetoidObject@{o o}) :=
  Sets_WellPoweredAt_up@{o so so} X.

(* CONTROL: at exactly N2's type, the conditional witness. *)
Definition p451_sets_pinned_untruncate@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) : WellPowered@{so o o so so} Sets@{o so} :=
  Sets_WellPowered_untruncate U.

(* CONTROL: the conditional witness IS the generic classifier witness. *)
Example p451_sets_untruncate_is_classifier (U : Untruncate) (X : SetoidObject) :
  Sets_WellPoweredAt_untruncate U X
    = @wp_of_classifier Sets Sets_Terminal Sets_HasPullbacks
        (Sets_Classifier U) X := eq_refl.

Fail Definition p451_n2_sets_up_at_pin@{o so | o < so, Set < o +} :
  WellPowered@{so o o so so} Sets@{o so} := fun X => Sets_WellPoweredAt_up X.

(** ** N3 (UNIVERSE): [Grp] one universe up is refused at the pin *)

(* CONTROL: the witness one universe up, per object. *)
Definition p451_grp_up@{o h | h < o, Set < o +} (G : Grp@{o h}) :=
  Grp_WellPoweredAt_up@{o o h} G.

Fail Definition p451_n3_grp_up_at_pin@{o h | h < o, Set < o +} :
  WellPowered@{o h h o o} Grp@{o h} := fun G => Grp_WellPoweredAt_up G.

(** ** N4-N6 (UNIVERSE): without well-poweredness, the class of subobjects
    is refused at the adjoint-functor regime *)

(* CONTROL: a family indexed at or below the homs needs no
   well-poweredness. *)
Definition p451_small_family@{o h j +| h < o, j <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (J : Type@{j}) (S : J → SubObj x) :=
  complete_intersection_IsIntersection comp S.

(* CONTROL: the class, given [WellPowered C]. *)
Definition p451_class_with_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) (P : SubObj x → Type@{h})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :=
  wellpowered_complete_has_intersections WP comp x P HP.

(* CONTROL: all subobjects, given [WellPowered C]. *)
Definition p451_all_with_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) := wellpowered_complete_intersection_all WP comp x.

(* CONTROL: N4's term with the objects at or below the homs. *)
Definition p451_class_small_objects@{o h +| o <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (P : SubObj x → Type@{h}) :=
  complete_intersection_IsIntersection comp
    (fun k : { m : SubObj x & P m } => `1 k).

Fail Definition p451_n4_class_no_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (P : SubObj x → Type@{h}) :=
  complete_intersection_IsIntersection comp
    (fun k : { m : SubObj x & P m } => `1 k).

(* CONTROL: N5's term with the objects at or below the homs. *)
Definition p451_all_small_objects@{o h +| o <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C) :=
  complete_intersection_IsIntersection comp (fun m : SubObj x => m).

Fail Definition p451_n5_all_no_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C) :=
  complete_intersection_IsIntersection comp (fun m : SubObj x => m).

(* CONTROL: the wide pullback of a small family of subobjects' monos. *)
Definition p451_wide_small@{o h j +| h < o, j <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (J : Type@{j}) (S : J → SubObj x) :=
  @wide_pullback C (Complete_HasWidePullbacks comp) J
    (fun k => Subobject.sub_dom (S k)) x (fun k => Subobject.sub_mono (S k)).

Fail Definition p451_n6_class_wide_pullback@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (P : SubObj x → Type@{h}) :=
  @wide_pullback C (Complete_HasWidePullbacks comp) { m : SubObj x & P m }
    (fun k => Subobject.sub_dom (`1 k)) x
    (fun k => Subobject.sub_mono (`1 k)).

(** ** N7 (UNIVERSE): the class of all subobjects at [Sets] *)

(* CONTROL: given [WellPowered Sets]. *)
Definition p451_sets_all_with_wp@{o so +| o < so +} (X : Sets@{o so})
  (WP : WellPowered Sets@{o so}) :=
  wellpowered_complete_intersection_all WP Sets_Complete X.

(* CONTROL: the [Untruncate] witness fed to the generic theorem. *)
Definition p451_sets_all_untruncate@{o so +| o < so, Set < o +}
  (U : Untruncate@{o}) (X : Sets@{o so}) :=
  wellpowered_complete_intersection_all (Sets_WellPowered_untruncate U)
    Sets_Complete X.

(* CONTROL: a family indexed at the carrier universe. *)
Definition p451_sets_small_family@{o so +| o < so +} (X : Sets@{o so})
  (J : Type@{o}) (S : J → SubObj X) :=
  complete_intersection_IsIntersection Sets_Complete S.

Fail Definition p451_n7_sets_all_no_wp@{o so +| o < so +} (X : Sets@{o so}) :=
  complete_intersection_IsIntersection Sets_Complete (fun m : SubObj X => m).

(** ** N8 (UNIVERSE), N9 (TYPING): arbitrary large families *)

Definition p451_image_resp {C : Category} {x : C} {J : Type}
  (S : J → SubObj x) :
  ∀ m m' : SubObj x, m ≈ m' → { j : J & S j ≈ m } → { j : J & S j ≈ m' }.
Proof.
  intros m m' e [j H]; exists j; etransitivity; [exact H | exact e].
Defined.

(* CONTROL: the typed image of a family indexed at or below the homs. *)
Definition p451_image_small@{o h j +| h < o, j <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) (J : Type@{j}) (S : J → SubObj x) :=
  wellpowered_complete_has_intersections WP comp x
    (fun m => { j : J & S j ≈ m }) (p451_image_resp S).

Fail Definition p451_n8_image_large@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) (J : Type@{o}) (S : J → SubObj x) :=
  wellpowered_complete_has_intersections WP comp x
    (fun m => { j : J & S j ≈ m }) (p451_image_resp S).

Section LargeFamily.

Context {C : Category} (comp : @Complete C) (WP : WellPowered C) (x : C).
Context {J : Type} (S : J → SubObj x).

Definition p451_trunc_class (m : SubObj x) : Prop :=
  ex (fun j : J => inhabited (S j ≈ m)).

Lemma p451_trunc_resp :
  ∀ m m' : SubObj x, m ≈ m' → p451_trunc_class m → p451_trunc_class m'.
Proof.
  intros m m' e [j [H]]; exists j; constructor; etransitivity;
    [exact H | exact e].
Qed.

(* CONTROL: the truncated image IS a class the [Prop] form accepts... *)
Definition p451_trunc_meet :=
  wellpowered_complete_has_intersections_prop WP comp x
    p451_trunc_class p451_trunc_resp.

(* CONTROL: ...and its intersection lies below every member of [S]. *)
Definition p451_trunc_le (j : J) : sub_le (`1 p451_trunc_meet) (S j) :=
  inter_le _ _ (`2 p451_trunc_meet)
    (S j; ex_intro _ j (inhabits (Equivalence_Reflexive (S j)))).

(* CONTROL: the greatest step with a [Type]-valued witness. *)
Definition p451_typed_greatest (v : SubObj x) (Hv : ∀ j, sub_le v (S j))
  (m : SubObj x) (w : { j : J & S j ≈ m }) : sub_le v m :=
  sub_le_trans _ _ _ (Hv (`1 w)) (sub_le_of_equiv _ _ (`2 w)).

(* CONTROL: the whole greatest step, over the intersection of the typed
   image, so that the truncation is the only difference from N9. *)
Definition p451_typed_meet :=
  wellpowered_complete_has_intersections WP comp x
    (fun m => { j : J & S j ≈ m }) (p451_image_resp S).

Definition p451_typed_greatest_full (v : SubObj x)
  (Hv : ∀ j, sub_le v (S j)) : sub_le v (`1 p451_typed_meet) :=
  ltac:(apply (inter_greatest _ _ (`2 p451_typed_meet));
        intros [m [j e]];
        exact (sub_le_trans _ _ _ (Hv j) (sub_le_of_equiv _ _ e))).

Fail Definition p451_n9_trunc_greatest (v : SubObj x)
  (Hv : ∀ j, sub_le v (S j)) : sub_le v (`1 p451_trunc_meet) :=
  ltac:(apply (inter_greatest _ _ (`2 p451_trunc_meet));
        intros [m [j [e]]];
        exact (sub_le_trans _ _ _ (Hv j) (sub_le_of_equiv _ _ e))).

End LargeFamily.

(** ** N10, N11 (UNIVERSE): the wide pullbacks, by which route and at
    which index *)

(* CONTROL: at a shape-object universe of [Set], the wide-equalizer shape
   is accepted. *)
Definition p451_wideparallel_at_set@{o h +| Set < h, h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h Set h o} C) (J : Type@{h}) :=
  comp (WideParallel J).

(* CONTROL: the route taken, at the regime. *)
Definition p451_wide_pullbacks_regime@{o h +| Set < h, h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) :
  HasWidePullbacks C := Complete_HasWidePullbacks comp.

Fail Definition p451_n10_wideparallel_regime@{o h +| Set < h, h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (J : Type@{h}) :=
  comp (WideParallel J).

(* CONTROL: a family indexed at the shape-object universe. *)
Definition p451_wide_index_small@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C)
  (J : Type@{h}) (A : J → C) (z : C) (f : ∀ j, A j ~> z) :=
  @complete_wide_pullback C comp J A z f.

Fail Definition p451_n11_wide_index_large@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C)
  (J : Type@{o}) (A : J → C) (z : C) (f : ∀ j, A j ~> z) :=
  @complete_wide_pullback C comp J A z f.

(** ** N12, N13 (CONVERSION): the lower bounds compute, the greatest-lower-
    bound factorization does not *)

Definition p451_IC : Category := Indiscrete bool.
Definition p451_IC_comp : @Complete p451_IC := Indiscrete_Complete true.
Definition p451_fam :
  ∀ j : Datatypes.unit,
    (fun _ => true : obj[p451_IC]) j ~{p451_IC}~> (true : obj[p451_IC]) :=
  fun _ => tt.
Definition p451_cone :
  ∀ j : Datatypes.unit,
    (false : obj[p451_IC]) ~{p451_IC}~> (fun _ => true : obj[p451_IC]) j :=
  fun _ => tt.
Definition p451_cone_commutes :
  ∀ i j : Datatypes.unit,
    p451_fam i ∘ p451_cone i ≈ p451_fam j ∘ p451_cone j :=
  fun _ _ => eq_refl.

(* CONTROL: the product mediator of the same completeness witness. *)
Example p451_product_mediator_computes :
  unique_obj
    (iprod_ump (fun _ : Datatypes.unit => (true : obj[p451_IC]))
       (p451_IC_comp _
          (DiscreteCat_Functor
             (fun _ : Datatypes.unit => (true : obj[p451_IC]))))
       (false : obj[p451_IC]) p451_cone) = tt := eq_refl.

(* CONTROL: the legs of the wide pullback, hence every [inter_le]. *)
Example p451_leg_computes :
  wide_pullback_proj (complete_wide_pullback p451_IC_comp p451_fam) tt = tt
  := eq_refl.

(* CONTROL: the mediator IS [tt] up to ≈, which in [Indiscrete] is
   Leibniz equality, by case analysis on [unit]. *)
Definition p451_mediator_equiv :
  unique_obj (ump_wide_pullbacks (complete_wide_pullback p451_IC_comp p451_fam)
                (false : obj[p451_IC]) p451_cone p451_cone_commutes) ≈ tt :=
  ltac:(destruct (unique_obj (ump_wide_pullbacks
                   (complete_wide_pullback p451_IC_comp p451_fam)
                   (false : obj[p451_IC]) p451_cone p451_cone_commutes));
        reflexivity).

Fail Example p451_n12_mediator_by_conversion :
  unique_obj (ump_wide_pullbacks (complete_wide_pullback p451_IC_comp p451_fam)
                (false : obj[p451_IC]) p451_cone p451_cone_commutes) = tt
  := eq_refl.

(* CONTROL: the GAFT equalizer's mediator, up to ≈. *)
Definition p451_gaft_equalizer := Complete_HasEqualizers p451_IC_comp.

Definition p451_gaft_mediator_equiv :
  unique_obj (eq_desc (`2 (`2 (@equalizer p451_IC p451_gaft_equalizer
                                  true true tt tt)))
                (z := false) tt eq_refl) ≈ tt :=
  ltac:(destruct (unique_obj (eq_desc (`2 (`2 (@equalizer p451_IC
                   p451_gaft_equalizer true true tt tt))) (z := false) tt
                   eq_refl)); reflexivity).

Fail Example p451_n13_gaft_mediator_by_conversion :
  unique_obj (eq_desc (`2 (`2 (@equalizer p451_IC p451_gaft_equalizer
                                  true true tt tt)))
                (z := false) tt eq_refl) = tt := eq_refl.

(** ** N14 (UNIVERSE): [SmallOrd^op]'s shape universe lies below its objects *)

(* CONTROL: the trivial witness, with the homs raised to the objects. *)
Definition p451_smallord_wp := trivial_small SmallOrd_op_Proset.

(* CONTROL: the theorem at [SmallOrd_op_Complete], over an abstract
   witness. *)
Definition p451_smallord_abstract (WP : WellPowered SmallOrd_op_Proset)
  (x : SmallOrd_op_Proset) :=
  wellpowered_complete_intersection_all WP SmallOrd_op_Complete x.

Fail Definition p451_n14_smallord_trivial (x : SmallOrd_op_Proset) :=
  wellpowered_complete_intersection_all (trivial_small SmallOrd_op_Proset)
    SmallOrd_op_Complete x.

(** ** N15 (UNIVERSE): Instance/Powerset.v's [Subsets_Complete], homs at
    [Set], meets the trivial witness nowhere *)

(* CONTROL: the literal [Subsets_Complete] at its own homs. *)
Definition p451_subsets_complete_at_set@{o +| Set < o +}
  (X : SetoidObject@{o o}) : @Complete (Subsets@{o Set} X) :=
  @Subsets_Complete X.

(* CONTROL: the free-hom-level restatement, fed to the theorem. *)
Definition p451_subsets_free@{o u +| Set < o, o <= u +}
  (X : SetoidObject@{o o}) (S : Subsets@{o u} X) :=
  wellpowered_complete_intersection_all (Subsets_WellPowered X)
    (Subsets_Complete_free X) S.

Fail Definition p451_n15_subsets_at_set@{o +| Set < o +}
  (X : SetoidObject@{o o}) (S : Subsets@{o Set} X) :=
  wellpowered_complete_intersection_all (trivial_small _)
    (@Subsets_Complete X) S.

(** ** N16 (UNIVERSE): the antichain with a top is well-powered at the pin
    only with its homs raised *)

(* CONTROL: one universe up, the trivial index. *)
Definition p451_at_trivial@{i o h t | i < o, h < t, h <= o +} :
  @WellPoweredAt@{o o o h t} AntichainTop@{i o h} None := AntichainTop_trivial.

(* CONTROL: at the pin, with [i < h]. *)
Definition p451_at_up@{i o h s t | i < o, i < h, h < t, o <= s, h <= s +} :
  @WellPoweredAt@{h o s h t} AntichainTop@{i o h} None :=
  AntichainTop_WellPoweredAt_up.

(* CONTROL: at N16's universes, the refutation. *)
Definition p451_at_refuted@{i o h w s t |
    i < o, h <= i, w <= h, h < t, o <= s, h <= s +}
  (WP : WellPowered@{o h w s t} AntichainTop@{i o h}) : False :=
  AntichainTop_not_WellPowered WP.

Fail Definition p451_n16_at_up_low_homs@{i o h s t |
    i < o, h <= i, h < t, o <= s, h <= s +} :
  @WellPoweredAt@{h o s h t} AntichainTop@{i o h} None :=
  AntichainTop_WellPoweredAt_up.

(** ** N17, N18 (TYPING), N19 (UNIVERSE): the routes to [Sets] at the pin
    without [Untruncate] *)

(* CONTROL: a preimage carried as data gives the element back. *)
Definition p451_typed_preimage@{o so | o < so +} (X A : SetoidObject@{o o})
  (m : A ~{Sets@{o so}}~> X) :
  { b : carrier X & { a : carrier A & m a ≈ b } } → carrier A :=
  fun p => `1 (`2 p).

Fail Definition p451_n17_inhabited_preimage@{o so | o < so +}
  (X A : SetoidObject@{o o}) (m : A ~{Sets@{o so}}~> X) :
  { b : carrier X | inhabited { a : carrier A & m a ≈ b } } → carrier A :=
  fun p => match proj2_sig p with inhabits q => `1 q end.

(* CONTROL: [Untruncate] inverts exactly the truncation N18 meets. *)
Definition p451_untruncated_preimage@{o so | o < so +} (U : Untruncate@{o})
  (X A : SetoidObject@{o o}) (m : A ~{Sets@{o so}}~> X) (b : carrier X)
  (h : Powerset_squash@{o} { a : carrier A & m a ≈ b }) : carrier A :=
  `1 (U _ h).

Fail Definition p451_n18_squashed_preimage@{o so | o < so +}
  (X A : SetoidObject@{o o}) (m : A ~{Sets@{o so}}~> X) (b : carrier X)
  (h : Powerset_squash@{o} { a : carrier A & m a ≈ b }) : carrier A :=
  `1 (h _ (fun q => q)).

(* CONTROL: the intersection over the pinned, conditional index. *)
Definition p451_sets_meet_pinned@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) (X : SetoidObject@{o o})
  (P : @SubObj Sets@{o so} X → Type@{o}) : @SubObj Sets@{o so} X :=
  @sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _ None
    (fun j : option { i : wp_index (Sets_WellPoweredAt_untruncate U X)
                    & P (wp_to (Sets_WellPoweredAt_untruncate U X) i) } =>
       match j with
       | None => @sub_top Sets@{o so} X
       | Some p => wp_to (Sets_WellPoweredAt_untruncate U X) (`1 p)
       end).

Fail Definition p451_n19_sets_meet_up@{o so | o < so, Set < o +}
  (X : SetoidObject@{o o})
  (P : @SubObj Sets@{o so} X → Type@{o}) : @SubObj Sets@{o so} X :=
  @sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _ None
    (fun j : option { i : wp_index (Sets_WellPoweredAt_up X)
                    & P (wp_to (Sets_WellPoweredAt_up X) i) } =>
       match j with
       | None => @sub_top Sets@{o so} X
       | Some p => wp_to (Sets_WellPoweredAt_up X) (`1 p)
       end).

(** ** N22 (INSTANCE): the class from completeness is a definition, and
    class search does not find it *)

(* CONTROL: the inhabitant #451 adds, supplied by hand. *)
Definition p451_svariety_hwp {S : UA.OpSignature} (E : UA.EqSignature S) :
  HasWidePullbacks (SVariety E) :=
  Complete_HasWidePullbacks (SVariety_Complete E).

Fail Definition p451_n22_hwp_by_search {S : UA.OpSignature}
  (E : UA.EqSignature S) : HasWidePullbacks (SVariety E) := _.

(* CONTROL: with BOTH the producer and the completeness witness registered
   locally, class search resolves the same hole, and what it finds IS the
   producer at [SVariety_Complete E].  Either registration alone leaves the
   hole refused (measured, see the header), so being a definition is not
   the whole of N22's reason. *)
Section SearchBoth.

#[local] Existing Instance Complete_HasWidePullbacks.
#[local] Hint Resolve SVariety_Complete : typeclass_instances.

Definition p451_n22_hwp_by_search_both {S : UA.OpSignature}
  (E : UA.EqSignature S) : HasWidePullbacks (SVariety E) := _.

Example p451_n22_search_finds {S : UA.OpSignature} (E : UA.EqSignature S) :
  p451_n22_hwp_by_search_both E
    = Complete_HasWidePullbacks (SVariety_Complete E) := eq_refl.

End SearchBoth.

(** ** N20, N21 (UNIVERSE): wide pullbacks from completeness do not feed the
    spanning-arrow solution set *)

(* CONTROL: the solution set over an abstract [HasWidePullbacks]. *)
Definition p451_span_abstract {S : UA.OpSignature} (E : UA.EqSignature S)
  (HWP : HasWidePullbacks (SVariety E))
  (GP : PreservesWidePullbacks (SVariety_Forget E)) (x : Sets) :=
  @spanning_solution_set _ _ (SVariety_Forget E) HWP GP x.

Fail Definition p451_n20_span_svariety {S : UA.OpSignature}
  (E : UA.EqSignature S) (GP : PreservesWidePullbacks (SVariety_Forget E))
  (x : Sets) :=
  @spanning_solution_set _ _ (SVariety_Forget E)
    (Complete_HasWidePullbacks (SVariety_Complete E)) GP x.

(* CONTROL: at [Sets] the class from completeness reads back at the
   universes of the direct instance. *)
Definition p451_sets_hwp_from_complete@{o so +| o < so +} :
  HasWidePullbacks@{o o so o} Sets@{o so} :=
  Complete_HasWidePullbacks Sets_Complete.

Definition p451_sets_hwp_direct@{o so +| o < so +} :
  HasWidePullbacks@{o o so o} Sets@{o so} := Sets_HasWidePullbacks.

(* CONTROL: the solution set at [Id[Sets]] over an abstract class. *)
Definition p451_span_sets_abstract (HWP : HasWidePullbacks Sets)
  (GP : PreservesWidePullbacks (@Id Sets)) (x : Sets) :=
  @spanning_solution_set _ _ (@Id Sets) HWP GP x.

Fail Definition p451_n21_span_sets (GP : PreservesWidePullbacks (@Id Sets))
  (x : Sets) :=
  @spanning_solution_set _ _ (@Id Sets)
    (Complete_HasWidePullbacks Sets_Complete) GP x.

(** ** Controls without a negative *)

(* FinSet, unconditionally at the pin, with its index read back. *)
Definition p451_finset_wp@{o h s t u v +| Set < u, h < t, o <= s, h <= s +} :
  WellPowered@{o h h s t} FinSet@{o h u v} := FinSet_WellPowered.

Example p451_finset_index (n : FinSet) :
  wp_index (FinSet_WellPowered n) = (Fin.t n → Fin.t 2) := eq_refl.

(* The unconditional instance with objects above homs. *)
Check (Indiscrete_types_has_intersections :
  ∀ (x : Indiscrete Type) (P : SubObj x → Type),
    (∀ m m' : SubObj x, m ≈ m' → P m → P m') →
    { w : SubObj x &
      IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w }).

(* The unconditional non-degenerate instance at the powerset lattice. *)
Check (Subsets_intersection_all_not_top :
  ∀ (X : SetoidObject) (x : carrier X),
    `1 (Subsets_intersection_all X subset_top) ≈ sub_top → False).

(* The bridge to SAFT's index, whose index IS the well-powered one. *)
Example p451_bridge_index (C : Category) (W : WellPowered C) (x : C) :
  sub_index (WellPowered_SubobjectIndex W x) = wp_index (W x) := eq_refl.

Check (@SubobjectIndex_not_exhaustive :
  ∀ (C : Category) (x : C),
    (SubObj x → sub_index (empty_SubobjectIndex x)) → False).

(* Formerly refused: [SAFT_of_WellPowered] with [WellPowered]'s [t] held
   strictly below [SAFT]'s slot [u]. *)
Section SAFTBinder.

Universes cobj dobj h u u1 u2 w s t.
Constraint h < u.
Constraint h < u1.
Constraint w <= h.
Constraint cobj <= s.
Constraint h <= s.
Constraint h < t.
Constraint t < u.

Context (C : Category@{cobj h h}) (D : Category@{dobj h h}) (U : C ⟶ D).
Context (comp : @Complete@{h h h cobj} C).
Context (cont : @PreservesImageLimit@{cobj h dobj h u1 h u h} C D U).
Context (G : Cogenerator@{h cobj h} C) (W : WellPowered@{cobj h w s t} C).
Context (cover : SubobjectCover@{u2 w h u h dobj cobj h} U comp G
                   (WellPowered_SubobjectIndex@{cobj h w s t} W)).

Definition p451_saft_direct :=
  SAFT U comp cont G (WellPowered_SubobjectIndex@{cobj h w s t} W) cover.
Definition p451_saft_of_wp := SAFT_of_WellPowered U comp cont G W cover.

End SAFTBinder.

(* Formerly refused: the [Id[Sets]] refutation with [cogen_prod]'s slot [u]
   declared strictly above, and strictly below, the object universe. *)
Section CoverAbove.

Universes cobj h u u2 u3.
Constraint Set < h.
Constraint h < cobj.
Constraint cobj < u.
Constraint u3 <= h.

Context (comp : @Complete@{h h h cobj} Sets@{h cobj}).
Context (G : Cogenerator@{h cobj h} Sets@{h cobj}).
Context (WP : ∀ x : Sets@{h cobj}, SubobjectIndex@{u3 cobj h} x).
Context (cover : SubobjectCover@{u2 u3 h u h cobj cobj h}
                   (@Id Sets@{h cobj}) comp G WP).

Definition p451_cover_above : False :=
  SubobjectCover_Id_Sets_absurd comp G WP cover.

End CoverAbove.

Section CoverBelow.

Universes cobj h u u2 u3.
Constraint Set < h.
Constraint h < u.
Constraint u < cobj.
Constraint u3 <= h.

Context (comp : @Complete@{h h h cobj} Sets@{h cobj}).
Context (G : Cogenerator@{h cobj h} Sets@{h cobj}).
Context (WP : ∀ x : Sets@{h cobj}, SubobjectIndex@{u3 cobj h} x).
Context (cover : SubobjectCover@{u2 u3 h u h cobj cobj h}
                   (@Id Sets@{h cobj}) comp G WP).

Definition p451_cover_below : False :=
  SubobjectCover_Id_Sets_absurd comp G WP cover.

End CoverBelow.

(** ** Guard block *)

Check @WellPoweredAt.
Check @wp_index.
Check @wp_to.
Check @wp_from.
Check @wp_to_from.
Check @wp_index_setoid.
Check @wp_from_resp.
Check @wp_from_to.
Check @WellPowered.
Check @CoWellPowered.
Check @quot_obj_is_sub_op.
Check @quot_setoid_is_sub_setoid_op.
Check @cowp_to_from.
Check @sub_opt_top.
Check @IsIntersection_drop_top.
Check @complete_intersection.
Check @complete_intersection_IsIntersection.
Check @wp_class_index.
Check @wp_class_family.
Check @IsIntersection_reindex.
Check @wp_complete_class_intersection.
Check @wellpowered_complete_has_intersections.
Check @wellpowered_intersection_is_small.
Check @wellpowered_complete_has_intersections_prop.
Check @wellpowered_complete_intersection_all.
Check @wellpowered_complete_least_subobject.
Check @cowellpowered_cocomplete_has_cointersections.
Check @cointersection_quot_le.
Check @wp_trivial.
Check @trivial_small.
Check @wp_groupoid.
Check @Groupoid_WellPowered.
Check @Groupoid_CoWellPowered.
Check @DiscreteCat_WellPowered.
Check @DiscreteCat_CoWellPowered.
Check @DiscreteCat_types_WellPowered.
Check @Indiscrete_WellPowered.
Check @Indiscrete_CoWellPowered.
Check @wp_of_classifier.
Check @Classifier_WellPowered.
Check @Indiscrete_Complete.
Check @Indiscrete_types_has_intersections.
Check @complete_wide_pullback.
Check @Complete_HasWidePullbacks.
Check @retract_paradox.
Check @AntichainTop.
Check @AntichainTop_not_WellPoweredAt.
Check @AntichainTop_not_WellPowered.
Check @AntichainTop_Set_not_WellPowered.
Check @AntichainTop_op_not_CoWellPowered.
Check @AntichainTop_trivial.
Check @AntichainTop_WellPoweredAt_up.
Check @FinSet_WellPowered.
Check @Sets_WellPoweredAt_up.
Check @Sets_CoWellPoweredAt_up.
Check @Sets_WellPoweredAt_untruncate.
Check @Sets_WellPowered_untruncate.
Check @Sets_wellpowered_intersection.
Check @Sets_intersection_all_empty.
Check @Grp_WellPoweredAt_up.
Check @Subsets_Complete_free.
Check @Subsets_WellPowered.
Check @Subsets_has_intersections.
Check @Subsets_intersection_all.
Check @Subsets_intersection_all_not_top.
Check @SubobjectIndex_of_WellPoweredAt.
Check @WellPowered_SubobjectIndex.
Check @SAFT_of_WellPowered.
Check @empty_SubobjectIndex.
Check @SubobjectIndex_not_exhaustive.
Check @SubobjectCover_Id_retract.
Check @SubobjectCover_Id_Sets_absurd.
Check @SubobjectCover_Id_Sets_absurd_at_SAFT.
