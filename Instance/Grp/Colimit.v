Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Disjoint.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Bicartesian.Matrix.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.FreeAFT.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Colimit.

Generalizable All Variables.

(* * * Colimits groups, adjoint 函子 定理 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/free+product
 nLab:      https://ncatlab.org/nlab/show/Grp
 Wikipedia: https://en.wikipedia.org/wiki/Free_product
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

   本文件给出余极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The solution set at a diagram *)

Section DiagonalSolutionSet.

Context {J : Category}.
Context (D : J ⟶ Grp).

(* 相关说明。 （已译） *)
Definition DGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (grp_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition dins (j : J) (a : carrier (grp_setoid (D j))) : FGWord DGen :=
  fg_insert DGen (j; a).

(* 相关说明。 （已译） *)
Record IsCoconeCong (Rq : FGWord DGen → FGWord DGen → Prop) : Prop := {
  cc_grp  : IsGrpCongruence Rq;
  cc_resp : ∀ j a b, a ≈ b → Rq (dins j a) (dins j b);
  cc_mul  : ∀ j a b, Rq (dins j (grp_mul (D j) a b))
                        (grp_mul (FreeGrpObject DGen) (dins j a) (dins j b));
  cc_nat  : ∀ j k (f : j ~{J}~> k) a,
              Rq (dins k (grp_map (fmap[D] f) a)) (dins j a)
}.

Definition DCongIdx : Type :=
  { Rq : FGWord DGen → FGWord DGen → Prop & IsCoconeCong Rq }.

Definition DQ (i : DCongIdx) : obj[Grp] := QGrp (`1 i) (cc_grp _ (`2 i)).

Definition dq_leg (i : DCongIdx) (j : J) : D j ~{Grp}~> DQ i.
Proof.
  unshelve refine (@Build_GrpHom' (D j) (DQ i)
                     {| morphism := dins j |} _).
  - intros a b Hab; exact (cc_resp _ (`2 i) j a b Hab).
  - intros a b; exact (cc_mul _ (`2 i) j a b).
Defined.

Definition dq_arr (i : DCongIdx) :
  D ~{[J, Grp]}~> fobj[@Diagonal Grp J] (DQ i).
Proof.
  unshelve refine (@Build_Transform' J Grp D (fobj[@Diagonal Grp J] (DQ i))
                     (fun j => dq_leg i j) _).
  intros j k f a; simpl.
  apply (gc_sym _ _ (cc_grp _ (`2 i))).
  exact (cc_nat _ (`2 i) j k f a).
Defined.

(* 相关说明。 （已译） *)
Section Cover.

Context (c : Grp) (h : D ~{[J, Grp]}~> fobj[@Diagonal Grp J] c).

Definition dflat : DGen ~{Sets}~> Grp_Forget c.
Proof using h.
  unshelve refine {| morphism := fun p => grp_map (transform[h] (`1 p)) (`2 p) |}.
  intros p q Hpq; simpl in Hpq; subst; reflexivity.
Defined.

Lemma dflat_gen (j : J) (a : carrier (grp_setoid (D j))) :
  fg_ev dflat (dins j a) ≈ grp_map (transform[h] j) a.
Proof using h. exact (free_grp_extend_generators DGen c dflat (j; a)). Qed.

(* Transparent on purpose: see the header. *)
Lemma dker_cocone : IsCoconeCong (fg_ker dflat).
Proof using h.
  constructor.
  - exact (fg_ker_is_cong dflat).
  - intros j a b Hab; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    rewrite !dflat_gen; now rewrite Hab.
  - intros j a b; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    unfold fg_ev; rewrite (grp_map_mul (free_grp_extend dflat)).
    fold (fg_ev dflat (dins j a)); fold (fg_ev dflat (dins j b)).
    fold (fg_ev dflat (dins j (grp_mul (D j) a b))).
    rewrite !dflat_gen.
    apply (grp_map_mul (transform[h] j)).
  - intros j k f a; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    rewrite !dflat_gen.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition dker_idx : DCongIdx := (fg_ker dflat; dker_cocone).

End Cover.

Definition Diagonal_Grp_solution_set : SolutionSet (@Diagonal Grp J) D.
Proof.
  unshelve refine (@Build_SolutionSet Grp ([J, Grp]) (@Diagonal Grp J) D
                     DCongIdx DQ dq_arr _).
  intros c h.
  exists (dker_idx c h).
  exists (fg_ker_med (dflat c h)).
  intros j a; simpl.
  exact (dflat_gen c h j a).
Defined.

End DiagonalSolutionSet.

(* 相关说明。 （已译） *)

Definition Grp_colim_via_GAFT (J : Category) :
  { K : [J, Grp] ⟶ Grp & K ⊣ @Diagonal Grp J } :=
  GAFT (@Diagonal Grp J) Grp_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_Grp_solution_set J).

Definition Grp_Cocomplete_via_GAFT : @Cocomplete Grp :=
  fun J F => Diagonal_left_adjoint_HasColimits (projT2 (Grp_colim_via_GAFT J)) F.

(* * ** Coproducts, coequalizers 始对象 （已译） *)

Definition Grp_FinitelyCocomplete_via_GAFT : @FinitelyCocomplete Grp :=
  Cocomplete_FinitelyCocomplete Grp_Cocomplete_via_GAFT.

Definition Grp_Cocartesian_via_GAFT : @Cocartesian Grp :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op Grp_FinitelyCocomplete_via_GAFT).

Definition Grp_HasCoequalizers_via_GAFT : HasCoequalizers Grp :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op Grp_FinitelyCocomplete_via_GAFT)).

Definition Grp_Initial_via_GAFT : @Initial Grp :=
  FinitelyCocomplete_Initial Grp_FinitelyCocomplete_via_GAFT.

(* 相关说明。 （已译） *)

(* The coproduct bifunctors agree up natural 同构: both left
 adjoint diagonal [Grp ⟶ Grp ∏ Grp]. （已译） *)
Definition Grp_coproduct_agrees :
  @InternalCoproductFunctor Grp Grp_Cocartesian_via_GAFT
    ≈ @InternalCoproductFunctor Grp Grp_Cocartesian :=
  left_adjoint_iso (Diagonal_Product Grp) _ _
    (@Diagonal_Coproduct_Adjunction Grp Grp_Cocartesian_via_GAFT)
    (@Diagonal_Coproduct_Adjunction Grp Grp_Cocartesian).

(* 相关说明。 （已译） *)
Definition Grp_free_product_iso@{u p +} (G H : Grp@{u p}) :
  @Coprod Grp@{u p} Grp_Cocartesian_via_GAFT G H
    ≅ @Coprod Grp@{u p} Grp_Cocartesian G H.
Proof.
  unshelve refine {|
    to   := @merge Grp Grp_Cocartesian_via_GAFT _ _ _
              (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H);
    from := @merge Grp Grp_Cocartesian _ _ _
              (@inl Grp Grp_Cocartesian_via_GAFT G H)
              (@inr Grp Grp_Cocartesian_via_GAFT G H) |}.
  - rewrite <- (@merge_comp Grp Grp_Cocartesian).
    rewrite (@inl_merge Grp Grp_Cocartesian_via_GAFT),
            (@inr_merge Grp Grp_Cocartesian_via_GAFT).
    exact (@merge_inl_inr Grp Grp_Cocartesian G H).
  - rewrite <- (@merge_comp Grp Grp_Cocartesian_via_GAFT).
    rewrite (@inl_merge Grp Grp_Cocartesian),
            (@inr_merge Grp Grp_Cocartesian).
    exact (@merge_inl_inr Grp Grp_Cocartesian_via_GAFT G H).
Defined.

Lemma Grp_free_product_iso_inl@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_iso G H) ∘ @inl Grp Grp_Cocartesian_via_GAFT G H
    ≈ @inl Grp Grp_Cocartesian G H.
Proof. exact (@inl_merge Grp Grp_Cocartesian_via_GAFT _ _ _ _ _). Qed.

Lemma Grp_free_product_iso_inr@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_iso G H) ∘ @inr Grp Grp_Cocartesian_via_GAFT G H
    ≈ @inr Grp Grp_Cocartesian G H.
Proof. exact (@inr_merge Grp Grp_Cocartesian_via_GAFT _ _ _ _ _). Qed.

(* The right-hand object above IS Instance/Grp/Pushout.v's free product. *)
Example Grp_Cocartesian_obj_is_free_product (G H : Grp) :
  @Coprod Grp Grp_Cocartesian G H = Grp_free_product G H := eq_refl.

(* The 始对象 trivial group. （已译） *)
Definition Grp_initial_agrees :
  @initial_obj Grp Grp_Initial_via_GAFT ≅ @initial_obj Grp Grp_Initial :=
  initial_unique Grp_Initial_via_GAFT Grp_Initial.

Lemma Grp_initial_via_GAFT_trivial
  (a b : carrier (grp_setoid (@initial_obj Grp Grp_Initial_via_GAFT))) :
  a ≈ b.
Proof.
  pose proof (iso_from_to Grp_initial_agrees a) as Ha.
  pose proof (iso_from_to Grp_initial_agrees b) as Hb.
  simpl in Ha, Hb.
  rewrite <- Ha, <- Hb.
  destruct (grp_map (to Grp_initial_agrees) a),
           (grp_map (to Grp_initial_agrees) b).
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition Grp_coequalizer_agrees_normal_closure {G H : Grp}
  (f : G ~{Grp}~> H) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _ f (@zero_mor Grp Grp_Zero G H))
    ≅ QuotientGrp (NormalClosure f) :=
  coequalizer_unique _ _
    (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _ f
                (@zero_mor Grp Grp_Zero G H))))
    (normal_closure_IsCoequalizer f).

(* 相关说明。 （已译） *)

(* Both injections free product monic, split copairing
 恒等 trivial map. （已译） *)
Definition Grp_inl_via_GAFT_Monic (G H : Grp) :
  Monic (@inl Grp Grp_Cocartesian_via_GAFT G H) :=
  @inl_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H.

Definition Grp_inr_via_GAFT_Monic (G H : Grp) :
  Monic (@inr Grp Grp_Cocartesian_via_GAFT G H) :=
  @inr_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H.

Lemma Grp_inl_via_GAFT_injective (G H : Grp) (a b : carrier (grp_setoid G)) :
  grp_map (@inl Grp Grp_Cocartesian_via_GAFT G H) a
    ≈ grp_map (@inl Grp Grp_Cocartesian_via_GAFT G H) b → a ≈ b.
Proof.
  exact (snd (Grp_injectivity_is_monic _) (Grp_inl_via_GAFT_Monic G H) a b).
Qed.

Lemma Grp_inr_via_GAFT_injective (G H : Grp) (a b : carrier (grp_setoid H)) :
  grp_map (@inr Grp Grp_Cocartesian_via_GAFT G H) a
    ≈ grp_map (@inr Grp Grp_Cocartesian_via_GAFT G H) b → a ≈ b.
Proof.
  exact (snd (Grp_injectivity_is_monic _) (Grp_inr_via_GAFT_Monic G H) a b).
Qed.

(* 相关说明。 （已译） *)
Definition Grp_HasPullbacks : HasPullbacks Grp :=
  FinitelyComplete_HasPullbacks (Complete_FinitelyComplete Grp_Complete).

(* 相关说明。 （已译） *)
Definition Grp_free_product_meet_trivial (G H : Grp) :
  @sub_meet Grp Grp_HasPullbacks _
     (@sub_inl Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
     (@sub_inr Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    ≈ @coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H :=
  @coproduct_injections_meet_trivial Grp Grp_Zero Grp_Cocartesian_via_GAFT
     Grp_HasPullbacks G H.

Example Grp_free_product_meet_bottom_is_trivial (G H : Grp) :
  sub_dom (@coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    = Grp_trivial := eq_refl.

(** ** Non-vacuity *)

Example Grp_free_product_via_GAFT_nontrivial :
  (∀ a b : carrier (grp_setoid (@Coprod Grp Grp_Cocartesian_via_GAFT Z2 Z2)),
     a ≈ b) → False.
Proof.
  intro Hall.
  apply Z2_nontrivial.
  apply (Grp_inl_via_GAFT_injective Z2 Z2).
  apply Hall.
Qed.
