Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Coq.Lists.List.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Stone-Cech+compactification

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** * The two points of the discrete two-point space *)

Definition sc_pt_bool@{o +} (b : bool) : Point_CH ~{CompHaus}~> Bool_CH :=
  (top_point Bool_Discrete@{o} b; I).

Definition sc_eval_pt@{c h +}
  (f : Point_CH ~{CompHaus : Category@{c h h}}~> Bool_CH) : bool :=
  continuous_map (`1 f) ttt.

Lemma sc_eval_pt_resp@{c h +}
  (u v : Point_CH ~{CompHaus : Category@{c h h}}~> Bool_CH) :
  u ≈ v → sc_eval_pt u = sc_eval_pt v.
Proof. intro H. exact (H ttt). Qed.

(** * Completeness at the hom universe is refuted (Freyd's core) *)

Theorem CompHaus_not_complete@{r s c h +}
  (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{r s h c} CompHaus) : False.
Proof.
  exact (freyd_no_separated_pair AI (sc_pt_bool true) (sc_pt_bool false) _ _
           (complete_iprod comp (fun _ : ai_index AI => Bool_CH))
           sc_eval_pt sc_eval_pt_resp eq_refl eq_refl).
Qed.

(* Informative excluded middle decides equality of objects. *)
Definition ObjDecEq_of_IEM@{e c h +} (E : IEM@{e}) (C : Category@{c h h}) :
  ObjDecEq C :=
  fun x y => match E (x = y) with
             | inl e => left e
             | inr n => right n
             end.

Theorem CompHaus_not_complete_IEM@{e r s c h +} (E : IEM@{e})
  (comp : @Complete@{r s h c} CompHaus) : False.
Proof.
  exact (CompHaus_not_complete
           (canonical_ArrowIndex (ObjDecEq_of_IEM E CompHaus)) comp).
Qed.

Theorem Top_not_complete@{r s h o +} (AI : ArrowIndex@{s h h} Top@{h o})
  (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (complete_iprod comp (fun _ : ai_index AI => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

Theorem Top_not_complete_IEM@{e r s h o +} (E : IEM@{e})
  (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete
           (canonical_ArrowIndex (ObjDecEq_of_IEM E Top)) comp).
Qed.

(** * Above the hom universe: an arrow index transported from [Top] *)

(* The homs of the full subcategory are [Top]'s paired with [True]
   ([Sub]), so an arrow index of [Top] indexes the arrows of [CompHaus] at
   every universe of its objects at or above the homs: the index never
   mentions them. *)
Definition CompHaus_ArrowIndex_of_Top@{s h o c +}
  (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (CompHaus : Category@{c h h}) :=
  @Build_ArrowIndex (CompHaus : Category@{c h h}) (ai_index AIT)
    (fun x y f => ai_enc AIT (`1 f))
    (fun x y m d => (ai_dec AIT m (`1 d); I))
    (fun x y f d => ai_dec_enc AIT (`1 f) (`1 d)).

Theorem CompHaus_not_complete_IEM_below@{e r s c h o +} (E : IEM@{e})
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h})) : False.
Proof.
  exact (CompHaus_not_complete
           (CompHaus_ArrowIndex_of_Top
              (canonical_ArrowIndex@{s h h} (ObjDecEq_of_IEM E Top@{h o})))
           comp).
Qed.

Theorem CompHaus_not_complete_IEM_above@{e h c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h})) : False.
Proof. exact (CompHaus_not_complete_IEM_below E comp). Qed.

(** * The adjunction itself is refuted: a universal arrow at a large set *)

(* The arrow index of [CompHaus], as a setoid with Leibniz equality. *)
Definition KSet@{s c h +} (AI : ArrowIndex@{s c h} CompHaus) :
  SetoidObject@{s s} :=
  {| carrier := ai_index AI; is_setoid := eq_Setoid (ai_index AI) |}.

Definition sc_phi_map@{c h +} (AI : ArrowIndex@{h c h} CompHaus)
  (phi : ai_index AI → bool) :
  KSet AI ~{Sets}~> CompHaus_Forget Bool_CH.
Proof.
  unshelve refine {| morphism := phi |}.
  all: intros a b e; simpl in *; destruct e; reflexivity.
Defined.

Theorem large_universal_arrow_refuted@{c h +}
  (AI : ArrowIndex@{h c h} CompHaus)
  (UA : UniversalArrow (C:=Sets) (KSet AI) CompHaus_Forget) : False.
Proof.
  pose (pm := sc_phi_map AI).
  pose (ext := fun phi => unique_obj (ump_universal_arrows UA (pm phi))).
  pose (dflt := ext (fun _ => true)).
  pose (Fam := fun k i =>
         continuous_map (`1 (ai_dec AI k dflt)) (@arrow _ _ _ _ UA i) : bool).
  apply (freyd_cantor_bool Fam).
  intro phi. exists (ai_enc AI (ext phi)). intro i.
  unfold Fam.
  rewrite (ai_dec_enc AI (ext phi) dflt (@arrow _ _ _ _ UA i)).
  pose proof (unique_property (ump_universal_arrows UA (pm phi)) i) as H.
  simpl in H. symmetry. exact H.
Qed.

Theorem StoneCech_adjunction_refuted_IEM@{e h s +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget }) : False.
Proof.
  pose (AI := canonical_ArrowIndex (ObjDecEq_of_IEM E CompHaus)).
  exact (large_universal_arrow_refuted AI
           (universal_arrow_of_adjunction (`2 A) (KSet AI))).
Qed.

(* The same at every object universe at or above the homs, through the
   index of [Top]. *)
Theorem StoneCech_adjunction_refuted_IEM_above@{e h s o c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False.
Proof.
  pose (AI := CompHaus_ArrowIndex_of_Top
                (canonical_ArrowIndex (ObjDecEq_of_IEM E Top@{h o}))).
  exact (large_universal_arrow_refuted AI
           (universal_arrow_of_adjunction (`2 A) (KSet AI))).
Qed.

(** * GAFT and SAFT consume the refuted hypothesis *)

Definition GAFT_CompHaus_IEM_vacuous@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) :
  ({ F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } * False)%type :=
  (GAFT_CompHaus_only_complete comp, CompHaus_not_complete_IEM E comp).

(* With the objects at or above the homs [taut_sols] no longer fits GAFT,
   so the solution sets are a hypothesis. *)
Definition GAFT_CompHaus_IEM_vacuous_above@{e h s c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h}))
  (sols : ∀ d : obj[Sets@{h s}], SolutionSet CompHaus_Forget d) :
  ({ F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
     & F ⊣ CompHaus_Forget } * False)%type :=
  (GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit sols,
   CompHaus_not_complete_IEM_above E comp).

Definition CompHaus_WellPowered@{c h t +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

(* SAFT at the inclusion, well-poweredness discharged: three hypotheses
   remain, and the completeness one is refuted under [IEM] at the
   instances COVERAGE records. *)
Definition SAFT_CompHaus_Incl@{s h +} (comp : @Complete@{s s h h} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Definition SAFT_Incl_vacuous@{s c h +} (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete AI comp).

Definition SAFT_Incl_IEM_vacuous@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete_IEM E comp).

(* The same at every shape universe SAFT accepts at the inclusion, the
   shapes below the objects included. *)
Definition SAFT_Incl_IEM_vacuous_below@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} (CompHaus : Category@{c h h}))
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete_IEM_below E comp).

(** * The classical-model obstruction, with no hypothesis beyond completeness *)

(* The index is the object type of the category [comp] is about: the local
   definition [C] makes the two one instance. *)
Definition big_inj@{r s c h +} (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi : obj[C] → bool) :
  top_carrier (`1 (complete_iprod_obj comp (fun _ : obj[C] => Bool_CH))) :=
  continuous_map
    (`1 (unique_obj
           (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
              (fun j => sc_pt_bool (phi j))))) ttt.

Lemma big_inj_injective@{r s c h +} (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi psi : obj[C] → bool) :
  big_inj comp phi ≈ big_inj comp psi → ∀ j, phi j = psi j.
Proof.
  intros E j.
  pose proof (unique_property
    (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
       (fun j => sc_pt_bool (phi j))) j ttt) as Hp.
  pose proof (unique_property
    (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
       (fun j => sc_pt_bool (psi j))) j ttt) as Hq.
  simpl in Hp, Hq.
  pose proof (proper_morphism
    (continuous_map
       (`1 (complete_iprod_proj comp (fun _ : obj[C] => Bool_CH) j)))
    _ _ E) as Hm.
  simpl in Hm.
  rewrite <- Hp, <- Hq. exact Hm.
Qed.

(** * A cogenerator of CompHaus with stable members gives DNE *)

(* The two-point space whose points are identified exactly when [P]. *)
Definition sc_yp_equiv@{o +} (P : Prop) (x y : bool) : Type@{o} :=
  (x = y \/ P).

Lemma sc_yp_equiv_Equivalence@{o +} (P : Prop) :
  Equivalence (sc_yp_equiv@{o} P).
Proof.
  unfold sc_yp_equiv; constructor.
  - intro x; left; reflexivity.
  - intros x y [e|p]; [left; symmetry; exact e | right; exact p].
  - intros x y z [e1|p] [e2|p2]; [left; congruence | right | right | right];
      assumption.
Qed.

Definition sc_YP@{o +} (P : Prop) : SetoidObject@{o o} :=
  {| carrier := bool;
     is_setoid := {| equiv := sc_yp_equiv P;
                     setoid_equiv := sc_yp_equiv_Equivalence P |} |}.

Lemma sc_yp_FinEnum@{o +} (P : Prop) :
  FinEnum (sc_YP P : SetoidObject@{o o}).
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | left; reflexivity].
  - exists false. split; [right; left; reflexivity | left; reflexivity].
Qed.

Definition YP_CH@{o +} (P : Prop) : CompHaus :=
  Discrete_CH (sc_YP P : SetoidObject@{o o}) (sc_yp_FinEnum P).

Definition sc_yp_const@{o +} (P : Prop) : YP_CH P ~{CompHaus}~> YP_CH P :=
  (Build_ContinuousMorphism (Discrete_Top@{o o} (sc_YP P))
     (Discrete_Top (sc_YP P))
     (const_morphism (sc_YP P) (sc_YP P) true)
     (fun U _ => open_const (Discrete_Top (sc_YP P)) (U true)); I).

Theorem CompHaus_cogenerator_stable_DNE@{k c h +}
  (G : Cogenerator@{k c h} CompHaus)
  (stable : ∀ j (a b : top_carrier (`1 (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P.
Proof.
  intros P nnP.
  assert (H : (@id CompHaus (YP_CH P)) ≈ sc_yp_const P).
  { apply (cog_separates G).
    intros j k b; simpl.
    apply stable; intro Hne.
    apply nnP; intro HP.
    apply Hne.
    apply (proper_morphism (continuous_map (`1 k))).
    right; exact HP. }
  destruct (H false) as [e|p]; [discriminate | exact p].
Qed.

(* The case of a single space: a [K] that separates the points of every
   compact Hausdorff space, the premise of Instance/Top/StoneCech.v's
   [KSeparated_of_unit_injective], costs the same when its points have
   ¬¬-stable equality. *)
Theorem CompHaus_point_separator_stable_DNE@{c h +}
  (K : (CompHaus : Category@{c h h}))
  (sepK : ∀ (Y : (CompHaus : Category@{c h h})) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (stable : ∀ a b : top_carrier (`1 K), ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P.
Proof.
  intros P nnP.
  destruct (sepK (YP_CH P) true false) as [e|p]; [| discriminate | exact p].
  intro k. apply stable. intro Hne. apply nnP. intro HP. apply Hne.
  apply (proper_morphism (continuous_map (`1 k))). right. exact HP.
Qed.
