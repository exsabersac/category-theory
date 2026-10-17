(*
   本文件为测试：ProbeSpecialInitial452。

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
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Sets.SpecialInitial.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe452_absent_name.

(** ** N1 (CONVERSION): the object IS the intersection, and not the product *)

(* CONTROL: the object readback, restated. *)
Example p452_obj@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = Subobject.sub_dom w :=
  eq_refl.

(* CONTROL: the zero-arrow readback, restated. *)
Example p452_zero@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w)
  (c : C) :
  @zero C (special_initial_object comp G w Hw) c
    = cogen_pullback_to comp G c
        ∘ `1 (inter_le _ _ Hw (cogen_pullback_sub comp G c)) :=
  eq_refl.

(* CONTROL: the conclusion in the type. *)
Definition p452_is_initial@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  IsInitialObj (Subobject.sub_dom w) :=
  special_initial_IsInitialObj comp G w Hw.

Fail Example p452_n1_obj_is_product@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = cogen_prod comp G :=
  eq_refl.

(** ** N2, N3 (UNIVERSE): the two donor collapses *)

(* CONTROL: [cogen_prod] at the collapsed index universe, [c = so]. *)
Definition p452_prod_at_so@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power], whose shape is a Σ over the index, takes an index
   universe below the shape universe. *)
Definition p452_power_low_index@{o h so c +| h <= so, c < so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (x : C) : C :=
  cogen_power comp G x.

Fail Definition p452_n2_prod_low_index@{o h so c +| h <= so, c < so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power] at the collapsed limit-datum universe, [r = so]. *)
Definition p452_power_at_so@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (x : C) : C :=
  cogen_power comp G x.

(* CONTROL: [cogen_prod] takes a limit-datum universe above the shape
   universe. *)
Definition p452_prod_high_datum@{o h r so +| h <= so, so < r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

Fail Definition p452_n3_power_high_datum@{o h r so +| h <= so, so < r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (x : C) : C :=
  cogen_power comp G x.

(** ** N4, N5 (UNIVERSE; N5 is P_H_le_so): small hom-sets, [h <= so] *)

(* INSTRUMENT: with the limit-datum universe [r] kept apart, the binder is
   formable at [so < h], so a refusal under it is about the body. *)
Definition p452_binder_ok@{o h r so +| so < h, h <= r +} {C : Category@{o h h}}
  (comp : @Complete@{r so h o} C) (G : Cogenerator@{so o h} C) (x : C) : C :=
  x.

(* With [r = so] the binder alone is refused, whatever the body. *)
Fail Definition p452_n4_binder_collapsed@{o h so +| so < h +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (x : C) : C :=
  x.

(* CONTROL: [cogen_prod] at [so < h <= r]. *)
Definition p452_prod_small_shape@{o h r so +| so < h, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power_limit]'s body at [h <= so <= r]. *)
Definition p452_power_limit_ok@{o h r so +| h <= so, so <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :=
  comp _ (Category.Instance.Discrete.DiscreteCat_Functor (cogen_power_fam G c)).

Fail Definition p452_n5_power_limit_small_shape@{o h r so +| so < h, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :=
  comp _ (Category.Instance.Discrete.DiscreteCat_Functor (cogen_power_fam G c)).

(** ** N6, N7 (UNIVERSE): the small-objects route at [so < o] *)

(* CONTROL: [special_initial_object_small]'s body, objects at or below the
   shape universe. *)
Definition p452_small_route_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* CONTROL: the library constant at the same universes. *)
Definition p452_small_const@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object_small comp G.

Fail Definition p452_n6_small_route@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* CONTROL: N7's term, the family's index explicit, at [o <= so]. *)
Definition p452_small_index_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :=
  @complete_intersection_IsIntersection C comp (cogen_prod comp G)
    (SubObj (cogen_prod comp G)) (fun m : SubObj (cogen_prod comp G) => m).

Fail Definition p452_n7_small_index@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :=
  @complete_intersection_IsIntersection C comp (cogen_prod comp G)
    (SubObj (cogen_prod comp G)) (fun m : SubObj (cogen_prod comp G) => m).

(** ** N8, N9 (UNIVERSE): the comparison with Freyd's construction *)

(* CONTROL: [special_vs_freyd]'s statement and body at [so = h]. *)
Definition p452_freyd_at_h@{o h +} {C : Category@{o h h}}
  (comp : @Complete@{h h h o} C) (G : Cogenerator@{h o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

Fail Definition p452_n8_freyd_above@{o h so +| h < so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

(* CONTROL: the weakly initial family of subobjects is formed with its index
   strictly below the homs. *)
Definition p452_wif_low@{o h w s t d +| w < h, h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{h d h o h} comp G)) :
  WeaklyInitialFamily C :=
  wif_of_cogenerator comp G W.

(* CONTROL: Freyd's construction takes it with the index AT the homs, which
   is [freyd_of_cogenerator]'s body. *)
Definition p452_freyd_wif_at_h@{o h s t d +| h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

Fail Definition p452_n9_freyd_wif_low@{o h w s t d +|
    w < h, h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

(** ** N10 (UNIVERSE): the small-objects form at [Sets] *)

(* CONTROL: the least-subobject form at the same universes. *)
Definition p452_sets_iem@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  sets_special_initial_IEM E.

(* CONTROL: its body, with [Sets_Complete], ascribed as in N10, and
   [Sets_Cogenerator_IEM E] named directly. *)
Definition p452_sets_iem_direct@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_IEM E)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Fail Definition p452_n10_small_at_sets@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object_small
    (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_IEM E).

(** ** N11, N12 (UNIVERSE; P_type_truth): the [Type]-valued truth setoid *)

(* [Type@{l}] under [iffT]: the classical object of truth values, with the
   library's [Type]-valued equivalence. *)
Definition p452_iff_setoid@{l m p +| l < m, l <= p +} :
  Setoid@{m p} Type@{l}.
Proof.
  refine (@Build_Setoid Type@{l} (fun P Q : Type@{l} => iffT P Q) _).
  constructor.
  - intro P; split; intro x; exact x.
  - intros P Q [a b]; split; assumption.
  - intros P Q R [a b] [c d]; split; intro x; auto.
Defined.

(* CONTROL: one level down, it IS an object of [Sets@{o so}]. *)
Definition p452_truth_low@{l o so +| l < o, o < so +} : obj[Sets@{o so}] :=
  @Build_SetoidObject Type@{l} p452_iff_setoid.

Fail Definition p452_n11_truth_at@{o so +| o < so +} : obj[Sets@{o so}] :=
  @Build_SetoidObject Type@{o} p452_iff_setoid.

(* CONTROL: the test map at a point [y0], for a setoid one level down. *)
Definition p452_char_low@{l o so +| l < o, o < so +}
  (Y : SetoidObject@{l l}) (y0 : carrier Y) :
  carrier Y → carrier (@Build_SetoidObject Type@{l} p452_iff_setoid) :=
  fun b => @equiv _ (is_setoid Y) y0 b.

Fail Definition p452_n12_char_at@{l o so +| l < o, o < so +}
  (Y : SetoidObject@{o o}) (y0 : carrier Y) :
  carrier Y → carrier (@Build_SetoidObject Type@{l} p452_iff_setoid) :=
  fun b => @equiv _ (is_setoid Y) y0 b.

(* CONTROL: the conditional cogenerator at the same universes. *)
Definition p452_cog_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : Cogenerator Sets@{o so} :=
  Sets_Cogenerator_untruncate U.

(** ** N13, N14 (UNIVERSE; P_large_cog): a large cogenerator of [Sets] *)

(* CONTROL: Instance/Sets/Cogenerator.v's [Sets_Cogenerator_large], every
   object tested by its identity, IS a [Cogenerator] of [Sets] with no
   hypothesis, at the universes that file's header states; its index is
   the type of all objects. *)
Definition p452_large_cog@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so} :=
  Sets_Cogenerator_large@{c o so}.

(* CONTROL: [cogen_prod] takes it over a completeness datum whose shape
   universe is the family's index universe.  The datum is hypothetical, a
   variable: [Sets_Complete] is [Complete@{o o o so}], its shape universe
   [o] and not the [c] above it. *)
Definition p452_large_prod_abstract@{c o so +| o < so, o < c +}
  (comp : @Complete@{c c o so} Sets@{o so}) : obj[Sets@{o so}] :=
  cogen_prod comp Sets_Cogenerator_large@{c o so}.

(* CONTROL: and so does the theorem, over any least subobject, the datum
   hypothetical as above. *)
Definition p452_large_sio_abstract@{c o so +| o < so, o < c +}
  (comp : @Complete@{c c o so} Sets@{o so})
  (w : SubObj (cogen_prod comp Sets_Cogenerator_large@{c o so}))
  (Hw : ∀ v : SubObj (cogen_prod comp Sets_Cogenerator_large@{c o so}),
          sub_le w v) :
  @Initial Sets@{o so} :=
  special_initial_object_least comp Sets_Cogenerator_large@{c o so} w Hw.

(* CONTROL: a small cogenerator's product at [Sets_Complete]. *)
Definition p452_small_prod_sets@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : obj[Sets@{o so}] :=
  cogen_prod (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_untruncate U).

Fail Definition p452_n13_large_prod_sets@{c o so +| o < so, o < c +} :
  obj[Sets@{o so}] :=
  cogen_prod (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    Sets_Cogenerator_large@{c o so}.

(* CONTROL: [sets_special_initial_untruncate]'s body, the small cogenerator
   at [Sets_Complete]. *)
Definition p452_small_sio_sets@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_untruncate U)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Fail Definition p452_n14_large_sio_sets@{c o so +| o < so, o < c +} :
  @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    Sets_Cogenerator_large@{c o so}
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

(** ** N15, N16 (UNIVERSE): [Sets^op] through well-poweredness *)

(* CONTROL: the corollary at [Sets^op] with the datum left free. *)
Definition p452_setsop_wp_free@{o so +| o < so +}
  (WP : WellPowered (Sets@{o so}^op)) : @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered WP setsop_comp setsop_cog.

(* CONTROL: the co-well-powered datum one universe up, per object. *)
Definition p452_sets_cowp_up@{o so +| o < so +} (X : SetoidObject@{o o}) :=
  Sets_CoWellPoweredAt_up@{o so so} X.

Fail Definition p452_n15_setsop_wp_up@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered (C := Sets@{o so}^op)
    (fun X => Sets_CoWellPoweredAt_up X) setsop_comp setsop_cog.

(* CONTROL: the per-object corollary at [Sets^op] with the datum left
   free. *)
Definition p452_setsop_wp_at_free@{o so +| o < so +}
  (W : WellPoweredAt (C := Sets@{o so}^op)
         (cogen_prod setsop_comp setsop_cog)) :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered_at setsop_comp setsop_cog W.

Fail Definition p452_n16_setsop_wp_at_up@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered_at setsop_comp setsop_cog
    (Sets_CoWellPoweredAt_up (cogen_prod setsop_comp setsop_cog)).

(** ** N17, N18 (CONVERSION): the objects at [Sets^op] and at [Sets] *)

(* CONTROL: at [Sets^op] the object IS the singleton. *)
Example p452_setsop_obj@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

Fail Example p452_n17_setsop_obj_empty@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

(* CONTROL: at [Sets] under [IEM] the object IS the empty setoid. *)
Example p452_sets_iem_obj@{o so +| o < so +} (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

Fail Example p452_n18_sets_iem_obj_singleton@{o so +| o < so +}
  (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

(** ** Controls without a negative *)

(* The degenerate generic witness reads back as [unit]. *)
Example p452_indiscrete_obj@{j o t +| j < o, j < t +} :
  @initial_obj (Indiscrete@{o j j} Type@{j}) Indiscrete_types_special_initial
    = (Datatypes.unit : Type@{j}) := eq_refl.

(* The non-degenerate generic witness has no members. *)
Check (Subsets_special_initial_is_empty :
  ∀ (X : SetoidObject) (G : Cogenerator (Subsets X)) (x : carrier X),
    (@initial_obj _ (Subsets_special_initial X G)
       : carrier (Powerset_Prop_obj X)) x → False).

(* The book's form at [Sets], from the #451 intersection. *)
Definition p452_sets_book@{o so +| Set < o, o < so +} (U : Untruncate@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object_book Sets_Complete (Sets_Cogenerator_untruncate U)
    (Sets_HasClassIntersections_untruncate U).

(* No family of copies of the terminal object cogenerates [Sets]. *)
Check (Sets_terminal_not_cogenerates :
  ∀ I : Type,
    ¬ (∀ (x y : SetoidObject) (f g : x ~{Sets}~> y),
         (I → ∀ k : y ~{Sets}~> @terminal_obj Sets Sets_Terminal,
                k ∘ f ≈ k ∘ g) → f ≈ g)).

(** ** Guard block *)

Check @equalizer_sub.
Check @least_sub_arrows_agree.
Check @cogen_prod_to_power.
Check @cogen_canonical_sub.
Check @complete_pullbacks.
Check @cogen_pullback_sub.
Check @cogen_pullback_to.
Check @special_initial_zero.
Check @special_initial_object_least.
Check @least_of_intersection_all.
Check @intersection_all_of_least.
Check @special_initial_object.
Check @special_initial_object_obj.
Check @special_initial_object_zero.
Check @special_initial_IsInitialObj.
Check @HasClassIntersections.
Check @special_initial_object_book.
Check @special_initial_object_book_obj.
Check @wellpowered_class_intersections.
Check @special_initial_object_wellpowered.
Check @special_initial_object_wellpowered_obj.
Check @special_initial_object_wellpowered_at.
Check @special_initial_object_wellpowered_at_obj.
Check @special_initial_object_small.
Check @special_weakly_initial.
Check @special_vs_freyd.
Check @wif_of_cogenerator.
Check @freyd_of_cogenerator.
Check @special_vs_freyd_of_cogenerator.
Check @Subsets_Cogenerator_empty.
Check @Subsets_Cogenerator_bot.
Check @Subsets_special_initial.
Check @Subsets_special_initial_obj.
Check @Subsets_special_initial_empty.
Check @Subsets_special_initial_bot.
Check @Subsets_special_vs_bot.
Check @Subsets_special_initial_is_empty.
Check @Subsets_special_initial_not_top.
Check @Indiscrete_Cogenerator_empty.
Check @Indiscrete_types_special_initial.
Check @Indiscrete_types_special_initial_obj.
Check @Sets_Cogenerator_untruncate.
Check @sets_cogenerator_untruncate_obj.
Check @sets_bool_char.
Check @Sets_Cogenerator_IEM.
Check @sets_cogenerator_IEM_obj.
Check @Sets_Cogenerator_large.
Check @Sets_terminal_not_cogenerates.
Check @setsop_comp.
Check @setsop_cog.
Check @setsop_point.
Check @setsop_L.
Check @setsop_L_least.
Check @setsop_special_initial.
Check @setsop_special_obj.
Check @setsop_special_vs_known.
Check @setsop_terminal_IsInitialObj.
Check @sets_special_initial_untruncate.
Check @sets_special_untruncate_obj.
Check @sets_special_initial_wellpowered.
Check @sets_special_wellpowered_obj.
Check @sets_special_wellpowered_vs_known.
Check @sets_special_wellpowered_empty.
Check @Sets_HasClassIntersections_untruncate.
Check @sets_special_initial_book.
Check @sets_special_book_obj.
Check @sets_special_book_vs_known.
Check @sets_special_initial_IEM.
Check @sets_special_IEM_obj.
Check @sets_special_initial_IEM_at_Set.
