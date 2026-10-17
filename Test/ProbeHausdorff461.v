(*
   本文件为测试：ProbeHausdorff461。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.GAFT.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Reflective.Colimit.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Hausdorff.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.
Require Import Category.Instance.Top.Hausdorff.TypeValued.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check p461_absent_name.

(** ** Instance/Top/Hausdorff.v: the solution-set index needs [Set < o] *)

(* CONTROL: the index at a universe above [Set]. *)
Definition p461_idx@{o +| Set < o +} (Pr : PTop@{o} → Type@{o})
  (X : PTop@{o}) : Type@{o} := PSolIdx@{o} Pr X.

(* N1 *)
Fail Definition p461_idx_at_set (Pr : PTop@{Set} → Type@{Set})
  (X : PTop@{Set}) : Type@{Set} := PSolIdx@{Set} Pr X.

(* CONTROL: the index's first two components at [Type@{o}], [Set < o]
   declared. *)
Definition p461_rel_part@{o +| Set < o +} (X : PTop@{o}) : Type@{o} :=
  { R : X → X → Prop & True }.

Definition p461_top_part@{o +| Set < o +} (X : PTop@{o}) : Type@{o} :=
  { T : (X → Prop) → Prop & True }.

(* N2 *)
Fail Definition p461_rel_part_closed@{o|} (X : PTop@{o}) : Type@{o} :=
  { R : X → X → Prop & True }.

(* N3 *)
Fail Definition p461_top_part_closed@{o|} (X : PTop@{o}) : Type@{o} :=
  { T : (X → Prop) → Prop & True }.

(** ** Instance/Top/Hausdorff.v: the two routes at [o := Set] *)

(* CONTROL: completeness, the direct reflector, its cocompleteness, the
   surjectivity of its unit, the restricted direct reflection and both
   refutations of a right adjoint, at points in [Set]. *)
Definition p461_complete_set@{so +| Set < so +} :
  @Complete@{Set Set Set so} Haus@{Set so} := Haus_Complete.

Definition p461_direct_set@{so +| Set < so +} :
  Reflective (PSepSub@{Set so} prem_T2@{Set}) := PT2_Reflective.

Definition p461_cocomplete_direct_set@{so +| Set < so +} :
  @Cocomplete Haus@{Set so} := Haus_Cocomplete_direct.

Definition p461_surjective_direct_set@{so +| Set < so +}
  (X : PTopCat@{Set so})
  (y : carrier (pt_carrier (`1 (fobj[reflector PT2_Reflective] X)))) :=
  Haus_unit_surjective_direct X y.

Definition p461_n0_direct_set@{so +| Set < so +} :
  Reflective (restrict_sub (PSepSub@{Set so} prem_T0@{Set})
                           (PSepSub@{Set so} prem_T1@{Set})) :=
  PT1_in_PT0_Reflective.

Definition p461_no_right_set@{so +| Set < so +}
  (R : PTopCat@{Set so} ⟶ Sub PTopCat@{Set so} Haus_Sub@{Set so})
  (A : Incl PTopCat@{Set so} Haus_Sub@{Set so} ⊣ R) : False :=
  Haus_inclusion_no_right_adjoint R A.

Definition p461_no_right_sets_set@{so +| Set < so +}
  (R : Sets@{Set so} ⟶ Sub PTopCat@{Set so} Haus_Sub@{Set so})
  (A : PForget@{Set so} ◯ Incl PTopCat@{Set so} Haus_Sub@{Set so} ⊣ R) :
  False := Haus_forget_no_right_adjoint R A.

(* N4 *)
Fail Definition p461_gaft_set@{so +| Set < so +} :
  Reflective Haus_Sub@{Set so} := Haus_reflective.

(* N5 *)
Fail Definition p461_cocomplete_set@{so +| Set < so +} :
  @Cocomplete Haus@{Set so} := Haus_Cocomplete.

(* N6 *)
Fail Definition p461_ex4_set@{so +| Set < so +} :
  (Reflective (restrict_sub (PSepSub@{Set so} prem_T0@{Set})
                            (PSepSub@{Set so} prem_T1@{Set}))
   * Reflective (restrict_sub (PSepSub@{Set so} prem_T1@{Set})
                              Haus_Sub@{Set so})
   * Reflective (restrict_sub Haus_Sub@{Set so}
                              (PFullSub@{Set so} PT3@{Set})))%type :=
  separation_axiom_reflections.

(* CONTROL: the two statements N4 and N6 refuse at [Set], at a universe
   above it. *)
Definition p461_gaft@{o so +| Set < o, o < so +} :
  Reflective Haus_Sub@{o so} := Haus_reflective.

Definition p461_ex4@{o so +| Set < o, o < so +} :
  (Reflective (restrict_sub (PSepSub@{o so} prem_T0@{o})
                            (PSepSub@{o so} prem_T1@{o}))
   * Reflective (restrict_sub (PSepSub@{o so} prem_T1@{o})
                              Haus_Sub@{o so})
   * Reflective (restrict_sub Haus_Sub@{o so}
                              (PFullSub@{o so} PT3@{o})))%type :=
  separation_axiom_reflections.

(** ** Instance/Top/Hausdorff.v: what reads back on the nose *)

(* CONTROL: the direct reflector's object is the largest Hausdorff
   quotient, at [eq_refl]. *)
Example p461_direct_obj@{o so +| o < so +} (X : PTopCat@{o so}) :
  `1 (fobj[reflector (PT2_Reflective : Reflective Haus_Sub@{o so})] X)
    = SepQuot prem_T2 X := eq_refl.

(* N7 *)
Fail Example p461_gaft_obj@{o so +| Set < o, o < so +} (X : PTopCat@{o so}) :
  `1 (fobj[reflector (Haus_reflective : Reflective Haus_Sub@{o so})] X)
    = SepQuot prem_T2 X := eq_refl.

(* CONTROL: at a Hausdorff space the reflection keeps the points, at
   [eq_refl], and is isomorphic to the space. *)
Example p461_lali_points@{o so +| o < so +} (X : Haus@{o so}) :
  carrier (pt_carrier (`1 (fobj[reflector PT2_Reflective]
                               (Incl PTopCat@{o so} Haus_Sub X))))
    = carrier (pt_carrier (`1 X)) := eq_refl.

Definition p461_counit_iso@{o so +| Set < o, o < so +} (X : Haus@{o so}) :
  reflector Haus_reflective (Incl PTopCat@{o so} Haus_Sub X) ≅[Haus@{o so}] X
  := Haus_counit_iso X.

(* N8 *)
Fail Example p461_lali@{o so +| o < so +} (X : Haus@{o so}) :
  `1 (fobj[reflector PT2_Reflective] (Incl PTopCat@{o so} Haus_Sub X))
    = `1 X := eq_refl.

(* CONTROL: the unit is the identity on points, at [eq_refl], and the
   reflector's action on a map agrees with the map at every point up to
   the reflection's equality, by the unit's naturality. *)
Example p461_unit_point@{o so +| o < so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X : PTopCat@{o so}) (x : carrier (pt_carrier X)) :
  pmap (@unit _ _ _ _ (PSep_adj prem L) X) x = x := eq_refl.

Lemma p461_fmap_equiv@{o so +| o < so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X Y : PTopCat@{o so})
  (f : X ~{PTopCat@{o so}}~> Y) (x : carrier (pt_carrier X)) :
  pmap (`1 (fmap[PSep_reflector prem L] f)) x ≈ pmap f x.
Proof.
  pose (A := PSep_adj prem L).
  assert (N : fmap[Incl PTopCat@{o so} (PSepSub prem)]
                (fmap[PSep_reflector prem L] f) ∘ @unit _ _ _ _ A X
              ≈ @unit _ _ _ _ A Y ∘ f).
  { rewrite <- (@to_adj_unit _ _ _ _ A _ _ (fmap[PSep_reflector prem L] f)).
    rewrite (@fmap_from_adj_unit _ _ _ _ A _ _ f).
    exact (@from_adj_comp_law _ _ _ _ A _ _ _). }
  exact (N x).
Qed.

(* N9 *)
Fail Example p461_fmap@{o so +| o < so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X Y : PTopCat@{o so})
  (f : X ~{PTopCat@{o so}}~> Y) (x : carrier (pt_carrier X)) :
  pmap (`1 (fmap[PSep_reflector prem L] f)) x = pmap f x := eq_refl.

(* CONTROL: the direct unit's section returns the point itself, at
   [eq_refl]. *)
Example p461_surjective_direct_point@{o so +| o < so +} (X : PTopCat@{o so})
  (y : carrier (pt_carrier (`1 (fobj[reflector PT2_Reflective] X)))) :
  projT1 (Haus_unit_surjective_direct X y) = y := eq_refl.

(* CONTROL: "we may take HX = X and η = 1": at a Hausdorff space the
   unit of the reflection by [GAFT] is an isomorphism of spaces, the
   counit its inverse. *)
Definition p461_unit_iso@{o so +| Set < o, o < so +} (X : Haus@{o so}) :
  { e : Incl PTopCat@{o so} Haus_Sub
          (reflector Haus_reflective (Incl PTopCat@{o so} Haus_Sub X))
        ~{PTopCat@{o so}}~> Incl PTopCat@{o so} Haus_Sub X &
    ((e ∘ @unit _ _ _ _ (reflective_adj Haus_reflective)
            (Incl PTopCat@{o so} Haus_Sub X) ≈ id) *
     (@unit _ _ _ _ (reflective_adj Haus_reflective)
        (Incl PTopCat@{o so} Haus_Sub X) ∘ e ≈ id))%type }.
Proof.
  exists (fmap[Incl PTopCat@{o so} Haus_Sub]
            (@counit _ _ _ _ (reflective_adj Haus_reflective) X)).
  split.
  - exact (@fmap_counit_unit _ _ _ _ (reflective_adj Haus_reflective) X).
  - pose (u := (@unit _ _ _ _ (reflective_adj Haus_reflective)
                   (Incl PTopCat@{o so} Haus_Sub X); I)
             : X ~{Haus@{o so}}~>
               reflector Haus_reflective (Incl PTopCat@{o so} Haus_Sub X)).
    exact (transitivity
             (symmetry (@counit_naturality _ _ _ _
                          (reflective_adj Haus_reflective) _ _ u))
             (@counit_fmap_unit _ _ _ _ (reflective_adj Haus_reflective)
                (Incl PTopCat@{o so} Haus_Sub X))).
Defined.

(** ** The Leibniz carrier: eliminating [ex] into the points' equality *)

(* CONTROL: into the Leibniz equality, a proposition, which the discrete
   two points' equality is by conversion. *)
Definition p461_elim_leibniz@{o} (a b : carrier (pt_carrier PBool@{o}))
  (H : ex (fun z : carrier (pt_carrier PBool@{o}) => z = a /\ z = b)) :
  a ≈ b :=
  match H return a = b with
  | ex_intro _ z (conj za zb) => eq_trans (eq_sym za) zb
  end.

(* N10 *)
Fail Definition p461_elim_setoid@{o} (a b : carrier (pt_carrier PBool@{o}))
  (H : ex (fun z : carrier (pt_carrier PBool@{o}) => z = a /\ z = b)) :
  a ≈ b :=
  match H with
  | ex_intro _ z (conj za zb) => eq_trans (eq_sym za) zb
  end.

(** ** Instance/Top/Hausdorff.v: Exercise 5's coequalizer and coproducts *)

(* CONTROL: [GlueQ]'s points are those of ℕ∞, its equality IS the
   relation [coeq_rel] generates, and the quotient map is the identity on
   points, all at [eq_refl]. *)
Example p461_glueq_points@{o so +| o < so +} :
  carrier (pt_carrier GlueQ@{o so _ _ _ _ _ _}) = option nat := eq_refl.

Example p461_glueq_equiv@{o so +| o < so +} (a b : option nat) :
  @equiv _ (pt_carrier GlueQ@{o so _ _ _ _ _ _}) a b
    = coeq_rel glue_f_set glue_g_set a b := eq_refl.

Example p461_glue_q_point@{o so +| o < so +} (x : option nat) :
  pmap glue_q@{o so _ _ _ _ _ _} x = x := eq_refl.

(* CONTROL: the binary coproduct of the two Hausdorff spaces of Exercise
   5 is Hausdorff. *)
Definition p461_bool_dec (a b : bool) : sumbool (a = b) (a = b → False) :=
  match a as a0, b as b0 return sumbool (a0 = b0) (a0 = b0 → False) with
  | true, true => left eq_refl
  | false, false => left eq_refl
  | true, false => right (fun e : true = false =>
                     match e in (_ = y) return (if y then True else False)
                     with eq_refl => I end)
  | false, true => right (fun e : false = true =>
                     match e in (_ = y) return (if y then False else True)
                     with eq_refl => I end)
  end.

Definition p461_sum_haus@{o u +| o < u +} :
  PHaus (PSigma@{o Set u} bool (fun b => if b then PNat@{o} else PConv@{o})) :=
  PHaus_coproduct_dec bool _ p461_bool_dec
    (fun b => match b return PHaus (if b then PNat@{o} else PConv@{o}) with
              | true => PNat_PHaus
              | false => PConv_PHaus
              end).

(** ** Instance/Top/Hausdorff/TypeValued.v: the vacuity at every instance *)

(* CONTROL: [GAFT_TopHaus_vacuous] at an instance whose universes are
   strictly apart: the subcategory's objects above [Top]'s homs, its
   predicate strictly between the points and the homs, its opens below
   the points.  A forced equation among them would be refused here. *)
Definition p461_vacuous_apart@{e h o u u0 u1 u2 u3 u4 u6 +| o < h, h < u1,
    h < u6, u2 < u, u3 < u, u2 < o, u3 < o, o < u, u < h, h < u4,
    u0 <= h, u4 <= u6 +} :=
  GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6}.

(* CONTROL: the refutation of completeness itself, for the objects of
   the subcategory strictly above [Top]'s homs. *)
Definition p461_not_complete_above@{e h o u u0 u1 u2 u3 u4 +| o < h,
    h < u1, u2 < u, u3 < u, u2 <= o, u3 <= o, u0 <= h, o <= u, h < u4,
    u <= u4 +} (E : IEM@{e})
  (comp : @Complete@{h h h u4}
            (Sub@{h h u u0 u4 h u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3})) : False :=
  TopHaus_not_complete_below_IEM E comp.

(* CONTROL: the two-point discrete space is Hausdorff with its separating
   opens strictly below its points. *)
Definition p461_bool_opens_below@{t p q o +| p < t, q < t, p < o, q < o,
    o <= t +} : IsHausdorff@{t p q o} Bool_Discrete@{o} :=
  tophaus_bool_hausdorff@{t p q o}.

(* N11 *)
Fail Definition p461_disc_opens_below@{t p q o +| p < t, q < t, p < o,
    q < o, o <= t +} (A : SetoidObject@{o o}) :
  IsHausdorff@{t p q o} (Discrete_Top@{o o} A) := Discrete_Hausdorff A.

(** ** Guard: every constant of the three targets *)

(* Instance/Top/Separation.v: 105 names. *)
Check Build_SepLaws.
Check PBool_PHaus.
Check PCofinite.
Check PCofinite_PT1.
Check PCofinite_not_PHaus.
Check PFullSub.
Check PFullSub_Full.
Check PHaus.
Check PHaus_PIsHausdorff.
Check PHaus_PT1.
Check PHaus_PropEquiv.
Check PHaus_distinct_not_notsep.
Check PHaus_in_PT1_Reflective.
Check PHaus_unfold.
Check PIsHausdorff.
Check PIsHausdorff_PHaus.
Check PIsHausdorff_PHaus_nn.
Check PNotSep.
Check PSep.
Check PSepObj.
Check PSepSpaces.
Check PSepSub.
Check PSep_Reflective.
Check PSep_adj.
Check PSep_mono.
Check PSep_reflector.
Check PSep_reflector_obj.
Check PSep_retract.
Check PSep_unit_point.
Check PSierpinski.
Check PSierpinski_PT0.
Check PSierpinski_not_PT1.
Check PT0.
Check PT0_Reflective.
Check PT1.
Check PT1_PT0.
Check PT1_Reflective.
Check PT1_in_PT0_Reflective.
Check PT1_in_PT0_obj.
Check PT1_in_PT0_unit_point.
Check PT2_Reflective.
Check PTwoIndisc_not_PT0.
Check SepLaws.
Check SepPremise.
Check SepQuot.
Check SepQuot_carrier.
Check SepQuot_equiv.
Check SepQuot_sep.
Check SepRel.
Check cof_open.
Check cof_open_inter.
Check cof_open_proper.
Check cof_open_respects.
Check cof_open_union.
Check cof_open_whole.
Check pnat_setoid.
Check prem_T0.
Check prem_T0_T1.
Check prem_T0_laws.
Check prem_T1.
Check prem_T1_T2.
Check prem_T1_laws.
Check prem_T2.
Check prem_T2_laws.
Check restrict_Reflective.
Check restrict_adj.
Check restrict_full.
Check restrict_obj.
Check restrict_reflector.
Check restrict_sub.
Check restrict_ua.
Check restrict_unit.
Check restrict_universal.
Check sep_ker.
Check sep_ker_SepRel.
Check sep_ker_of.
Check sep_ker_to.
Check sep_le_add_l.
Check sep_le_add_r.
Check sep_le_trans.
Check sep_not_succ_le.
Check sep_proj.
Check sep_pull_cont.
Check sep_q.
Check sep_qopen.
Check sep_setoid.
Check sep_ua.
Check sep_universal.
Check sepeq.
Check sepeq_of_equiv.
Check sepeq_refl.
Check sepeq_sym.
Check sepeq_trans.
Check sepquot_med.
Check sepquot_med_resp.
Check sepquot_med_setoid.
Check sier_open.
Check sier_open_inter.
Check sier_open_proper.
Check sier_open_respects.
Check sier_open_union.
Check sier_open_whole.
Check sl_anti.
Check sl_equiv.
Check sl_pull.

(* Instance/Top/Hausdorff.v: 115 names. *)
Check Build_TopPresentation.
Check GlueQ.
Check GlueQ_not_PHaus.
Check GlueQ_not_PIsHausdorff.
Check GlueQ_notsep.
Check GlueQ_points_apart.
Check GlueQ_reflection_glues.
Check HConv.
Check HNat.
Check Haus.
Check Haus_Cocomplete.
Check Haus_Cocomplete_direct.
Check Haus_Complete.
Check Haus_Forget_left_adjoint.
Check Haus_Forget_left_adjoint_direct.
Check Haus_Incl_continuous.
Check Haus_Sub.
Check Haus_colimit_apex.
Check Haus_counit_iso.
Check Haus_forget_no_right_adjoint.
Check Haus_in_PT1_reflective_GAFT.
Check Haus_inclusion_no_right_adjoint.
Check Haus_reflective.
Check Haus_reflectors_iso.
Check Haus_unit_surjective.
Check Haus_unit_surjective_direct.
Check PBool_PReg.
Check PBool_PT3.
Check PClosureIn.
Check PComb.
Check PComb_PHaus.
Check PComb_not_PReg.
Check PConv_PHaus.
Check PConv_PIsHausdorff.
Check PConv_tail_open.
Check PFull_Reflective_GAFT.
Check PFull_left_adjoint_GAFT.
Check PFull_sols.
Check PHaus_coproduct.
Check PHaus_coproduct_dec.
Check PNat.
Check PNat_PHaus.
Check PReg.
Check PRegOpens.
Check PReg_PT0_PHaus.
Check PSep_closed.
Check PSep_img.
Check PSep_reflective_GAFT.
Check PSolIdx.
Check PT0_reflective_GAFT.
Check PT1_in_PT0_reflective_GAFT.
Check PT1_reflective_GAFT.
Check PT3.
Check PT3_closed.
Check PT3_img.
Check PT3_in_Haus_reflective_GAFT.
Check PT3_reflective_GAFT.
Check TopPresentation.
Check comb_c.
Check comb_inf.
Check comb_k.
Check comb_open.
Check comb_open_c.
Check comb_open_inf.
Check comb_open_inter.
Check comb_open_k.
Check comb_open_proper.
Check comb_open_respects.
Check comb_open_union.
Check comb_open_whole.
Check comb_pt.
Check comb_pt_ind.
Check comb_pt_rec.
Check comb_pt_rect.
Check comb_pt_sind.
Check comb_setoid.
Check double_succ.
Check glue_IsCoequalizer.
Check glue_coeq.
Check glue_f.
Check glue_f_h.
Check glue_f_set.
Check glue_g.
Check glue_g_h.
Check glue_g_set.
Check glue_none_inv.
Check glue_q.
Check img_PReg.
Check img_mor.
Check img_rel.
Check img_space.
Check img_top.
Check img_valid.
Check plimit_PReg.
Check plimit_PSep.
Check pres_base.
Check pres_cont.
Check pres_inter.
Check pres_proj.
Check pres_proper.
Check pres_refl.
Check pres_respects.
Check pres_setoid.
Check pres_space.
Check pres_sym.
Check pres_trans.
Check pres_union.
Check pres_whole.
Check psigma_img.
Check psigma_img_open.
Check psigma_summand_open.
Check psol_arr.
Check psol_obj.
Check sep_dec_uip.
Check separation_axiom_reflections.

(* Instance/Top/Hausdorff/TypeValued.v: 48 names. *)
Check Build_TSepLaws.
Check GAFT_TopHaus.
Check GAFT_TopHaus_vacuous.
Check IsHausdorff_TSep2_nn.
Check TSep.
Check TSepLaws.
Check TSepObj.
Check TSepPremise.
Check TSepQuot.
Check TSepQuot_sep.
Check TSepRel.
Check TSepSpaces.
Check TSepSub.
Check TSep_Full.
Check TSep_Reflective.
Check TSep_adj.
Check TSep_reflector.
Check TopHaus_ArrowIndex_of_Top.
Check TopHaus_Bool.
Check TopHaus_Point.
Check TopHaus_not_complete.
Check TopHaus_not_complete_below_IEM.
Check TopT2_Reflective.
Check tl_equiv.
Check tl_pull.
Check tophaus_bool_hausdorff.
Check tophaus_point_hausdorff.
Check tophaus_pt_bool.
Check tprem_T2.
Check tprem_T2_laws.
Check tsep_ker.
Check tsep_ker_TSepRel.
Check tsep_ker_of.
Check tsep_ker_to.
Check tsep_med.
Check tsep_med_resp.
Check tsep_med_setoid.
Check tsep_proj.
Check tsep_q.
Check tsep_qopen.
Check tsep_setoid.
Check tsep_ua.
Check tsep_universal.
Check tsepeq.
Check tsepeq_of_equiv.
Check tsepeq_refl.
Check tsepeq_sym.
Check tsepeq_trans.
