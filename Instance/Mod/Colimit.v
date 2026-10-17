Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Free.

Generalizable All Variables.

(* * * Colimits R-modules, adjoint 函子 定理 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Mod
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_modules
 Wikipedia: https://en.wikipedia.org/wiki/Direct_sum_of_modules

   本文件给出余极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The solution set at a diagram *)

Section ModDiagonalSolutionSet.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes a c p o x jo.
Constraint Set < o, c < o, c < x, p <= a, c <= a, a <= o, jo <= c.

Context {R : RingObject@{a c p}}.
Context {J : Category@{jo c c}}.
Context (D : J ⟶ RMod@{o x a p c} R).

(* 相关说明。 （已译） *)
Definition MGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (cmon_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition mins (j : J) (a : carrier (cmon_setoid (D j))) : @FVTerm R MGen :=
  @fv_gen R MGen (existT (fun j => carrier (cmon_setoid (D j))) j a).

(* A congruence free-module terms: 等价 关系 that
 contains term model's own 关系 [fv_eq] compatible with
 three formers. （已译） *)
Record IsModCongruence (Rq : @FVTerm R MGen → @FVTerm R MGen → Prop) : Prop := {
  mc_refl  : ∀ s, Rq s s;
  mc_sym   : ∀ s t, Rq s t → Rq t s;
  mc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  mc_gen   : ∀ s t, fv_eq s t → Rq s t;
  mc_plus  : ∀ s s' t t', Rq s s' → Rq t t' → Rq (fv_plus s t) (fv_plus s' t');
  mc_neg   : ∀ s s', Rq s s' → Rq (fv_neg s) (fv_neg s');
  mc_smul  : ∀ r s s', Rq s s' → Rq (fv_smul r s) (fv_smul r s')
}.

(* 相关说明。 （已译） *)
Record IsModCoconeCong (Rq : @FVTerm R MGen → @FVTerm R MGen → Prop) : Prop := {
  mcc_mod  : IsModCongruence Rq;
  mcc_resp : ∀ j a b, a ≈ b → Rq (mins j a) (mins j b);
  mcc_zero : ∀ j, Rq (mins j (cmon_zero (D j))) fv_zero;
  mcc_plus : ∀ j a b, Rq (mins j (cmon_plus (D j) a b))
                         (fv_plus (mins j a) (mins j b));
  mcc_smul : ∀ j r a, Rq (mins j (rm_smul (D j) r a)) (fv_smul r (mins j a));
  mcc_nat  : ∀ j k (f : j ~{J}~> k) a,
               Rq (mins k (cmon_map (rm_hom (fmap[D] f)) a)) (mins j a)
}.

Definition MDCongIdx : Type :=
  { Rq : @FVTerm R MGen → @FVTerm R MGen → Prop & IsModCoconeCong Rq }.

(* NAMED, for [PropEquiv_of_relation]'s sake (Instance/Mod/TensorAFT.v's
   [QMod_Setoid] records why). *)
Definition MDQ_Setoid (i : MDCongIdx) : Setoid (@FVTerm R MGen) :=
  {| equiv := `1 i
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := mc_refl  _ (mcc_mod _ (`2 i))
        ; Equivalence_Symmetric  := mc_sym   _ (mcc_mod _ (`2 i))
        ; Equivalence_Transitive := mc_trans _ (mcc_mod _ (`2 i)) |} |}.

Lemma MDQ_smul_respects (i : MDCongIdx) :
  Proper (equiv ==> `1 i ==> `1 i) (@fv_smul R MGen).
Proof.
  intros r r' Hr s s' Hs.
  apply (mc_trans _ (mcc_mod _ (`2 i)) _ (fv_smul r s')).
  - exact (mc_smul _ (mcc_mod _ (`2 i)) r _ _ Hs).
  - exact (mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_smul Hr (fv_refl s'))).
Qed.

(* 相关说明。 （已译） *)
Definition MDQ (i : MDCongIdx) : obj[RMod R] :=
  {| rm_ab := {|
       ab_cmon := {|
         cmon_setoid :=
           {| carrier := @FVTerm R MGen; is_setoid := MDQ_Setoid i |};
         cmon_zero := @fv_zero R MGen;
         cmon_plus := @fv_plus R MGen;
         cmon_plus_respects := fun _ _ Hs _ _ Ht =>
           mc_plus _ (mcc_mod _ (`2 i)) _ _ _ _ Hs Ht;
         cmon_plus_assoc := fun s t u =>
           mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_assoc s t u);
         cmon_plus_comm := fun s t =>
           mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_comm s t);
         cmon_plus_zero_l := fun s =>
           mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_zero_l s);
         cmon_prop := @PropEquiv_of_relation _ (MDQ_Setoid i) (`1 i)
                        (fun _ _ h => h) (fun _ _ h => h)
       |};
       ab_neg := @fv_neg R MGen;
       ab_neg_respects := fun _ _ Hs => mc_neg _ (mcc_mod _ (`2 i)) _ _ Hs;
       ab_neg_left := fun s => mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_neg_l s)
     |};
     rm_smul := @fv_smul R MGen;
     rm_smul_respects := MDQ_smul_respects i;
     rm_smul_distr_l := fun r s t =>
       mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_smul_distr_l r s t);
     rm_smul_distr_r := fun r r' s =>
       mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_smul_distr_r r r' s);
     rm_smul_assoc := fun r r' s =>
       mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_smul_assoc r r' s);
     rm_smul_one := fun s => mc_gen _ (mcc_mod _ (`2 i)) _ _ (fe_smul_one s)
  |}.

Definition mdq_leg (i : MDCongIdx) (j : J) : D j ~{RMod R}~> MDQ i.
Proof.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact (mins j).
  - intros a b Hab; exact (mcc_resp _ (`2 i) j a b Hab).
  - exact (mcc_zero _ (`2 i) j).
  - intros a b; exact (mcc_plus _ (`2 i) j a b).
  - intros r a; exact (mcc_smul _ (`2 i) j r a).
Defined.

Definition mdq_arr (i : MDCongIdx) :
  D ~{[J, RMod R]}~> fobj[@Diagonal (RMod R) J] (MDQ i).
Proof.
  unshelve refine (@Build_Transform' J (RMod R) D
                     (fobj[@Diagonal (RMod R) J] (MDQ i))
                     (fun j => mdq_leg i j) _).
  intros j k f a; simpl.
  apply (mc_sym _ (mcc_mod _ (`2 i))).
  exact (mcc_nat _ (`2 i) j k f a).
Defined.

(* 相关说明。 （已译） *)
Section Cover.

Context (M : obj[RMod R]) (h : D ~{[J, RMod R]}~> fobj[@Diagonal (RMod R) J] M).

Definition mflat : MGen ~{Sets}~> RMod_Forget R M.
Proof using h.
  unshelve refine {| morphism := fun q =>
                       cmon_map (rm_hom (transform[h] (`1 q))) (`2 q) |}.
  intros q q' Hq; simpl in Hq; subst; reflexivity.
Defined.

Definition mker : @FVTerm R MGen → @FVTerm R MGen → Prop :=
  fun s t => @pequiv _ _ (cmon_prop M) (fv_eval mflat s) (fv_eval mflat t).

(* 相关说明。 （已译） *)
Lemma mker_cocone : IsModCoconeCong mker.
Proof using h.
  unfold mker.
  constructor; [constructor|..].
  - intro s; apply (@pequiv_from _ _ (cmon_prop M)); reflexivity.
  - intros s t Hst; apply (@pequiv_from _ _ (cmon_prop M)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop M) _ _ Hst).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop M)).
    transitivity (fv_eval mflat t);
      [ exact (@pequiv_to _ _ (cmon_prop M) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop M) _ _ H2) ].
  - intros s t Hst; apply (@pequiv_from _ _ (cmon_prop M));
      exact (fv_eval_respects M mflat s t Hst).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    exact (cmon_plus_respects M _ _ (@pequiv_to _ _ (cmon_prop M) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop M) _ _ H2)).
  - intros s s' H1; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    exact (ab_neg_respects M _ _ (@pequiv_to _ _ (cmon_prop M) _ _ H1)).
  - intros r s s' H1; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    exact (rm_smul_respects M _ _ (reflexivity r) _ _
             (@pequiv_to _ _ (cmon_prop M) _ _ H1)).
  - intros j a b Hab; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    now rewrite Hab.
  - intros j; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    exact (cmon_map_zero (rm_hom (transform[h] j))).
  - intros j a b; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    exact (cmon_map_plus (rm_hom (transform[h] j)) a b).
  - intros j r a; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    exact (rm_map_smul (transform[h] j) r a).
  - intros j k f a; apply (@pequiv_from _ _ (cmon_prop M)); simpl.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition mker_idx : MDCongIdx := existT _ mker mker_cocone.

(* 相关说明。 （已译） *)
Definition mker_med : MDQ mker_idx ~{RMod R}~> M.
Proof using h.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact (fv_eval mflat).
  - intros s t H; exact (@pequiv_to _ _ (cmon_prop M) _ _ H).
  - simpl; reflexivity.
  - intros s t; simpl; reflexivity.
  - intros r s; simpl; reflexivity.
Defined.

End Cover.

Definition Diagonal_RMod_solution_set : SolutionSet (@Diagonal (RMod R) J) D.
Proof.
  unshelve refine (@Build_SolutionSet (RMod R) ([J, RMod R])
                     (@Diagonal (RMod R) J) D MDCongIdx MDQ mdq_arr _).
  intros M h.
  exists (mker_idx M h).
  exists (mker_med M h).
  intros j a; simpl.
  reflexivity.
Defined.

End ModDiagonalSolutionSet.

(* 相关说明。 （已译） *)

Definition RMod_colim_via_GAFT@{a c p o x jo +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, jo <= c +}
  (R : RingObject@{a c p}) (J : Category@{jo c c}) :
  { K : [J, RMod@{o x a p c} R] ⟶ RMod@{o x a p c} R
  & K ⊣ @Diagonal (RMod@{o x a p c} R) J } :=
  GAFT (@Diagonal (RMod R) J) (RMod_Complete R)
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_RMod_solution_set R J).

Definition RMod_Cocomplete_via_GAFT@{a c p o x so +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, so <= c +}
  (R : RingObject@{a c p}) : @Cocomplete@{c so c o} (RMod@{o x a p c} R) :=
  fun J F =>
    Diagonal_left_adjoint_HasColimits (projT2 (RMod_colim_via_GAFT R J)) F.

(* 相关说明。 （已译） *)

Definition RMod_FinitelyCocomplete_via_GAFT@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : @FinitelyCocomplete (RMod@{o x a p c} R) :=
  Cocomplete_FinitelyCocomplete (RMod_Cocomplete_via_GAFT R).

Definition RMod_Cocartesian_via_GAFT@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : @Cocartesian (RMod@{o x a p c} R) :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op
       (RMod_FinitelyCocomplete_via_GAFT R)).

Definition RMod_HasCoequalizers_via_GAFT@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : HasCoequalizers (RMod@{o x a p c} R) :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op
          (RMod_FinitelyCocomplete_via_GAFT R))).

Definition RMod_Initial_via_GAFT@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : @Initial (RMod@{o x a p c} R) :=
  FinitelyCocomplete_Initial (RMod_FinitelyCocomplete_via_GAFT R).

(** ** Non-vacuity *)

(* The initial module 定理 produces zero module: the
 恒等 zero homomorphism two arrows out it. （已译） *)
Lemma RMod_initial_via_GAFT_trivial@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}}
  (a0 : carrier (cmon_setoid
          (@initial_obj (RMod@{o x a p c} R) (RMod_Initial_via_GAFT R)))) :
  a0 ≈ cmon_zero _.
Proof.
  exact (@zero_unique (RMod R) (RMod_Initial_via_GAFT R) _ id rmod_hom_zero a0).
Qed.

(* The left injection coproduct split copairing the
 恒等 zero homomorphism ... （已译） *)
Lemma RMod_inl_via_GAFT_retract@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (M N : obj[RMod@{o x a p c} R]) :
  @merge (RMod R) (RMod_Cocartesian_via_GAFT R) _ _ _ id rmod_hom_zero
    ∘ @inl (RMod R) (RMod_Cocartesian_via_GAFT R) M N ≈ id.
Proof. exact (@inl_merge (RMod R) (RMod_Cocartesian_via_GAFT R) _ _ _ _ _). Qed.

(* ... and is therefore injective. *)
Lemma RMod_inl_via_GAFT_injective@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (M N : obj[RMod@{o x a p c} R])
  (a0 b0 : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (@inl (RMod R) (RMod_Cocartesian_via_GAFT R) M N)) a0
    ≈ cmon_map (rm_hom (@inl (RMod R) (RMod_Cocartesian_via_GAFT R) M N)) b0 →
  a0 ≈ b0.
Proof.
  intro H.
  pose proof (RMod_inl_via_GAFT_retract M N a0) as Ha.
  pose proof (RMod_inl_via_GAFT_retract M N b0) as Hb.
  simpl in Ha, Hb.
  rewrite <- Ha, <- Hb, H.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Example RMod_coproduct_via_GAFT_nontrivial@{c o x +| Set < c, c < o, c < x +} :
  (∀ a0 b0 : carrier (cmon_setoid
       (@Coprod (RMod@{o x c c c} Int_Ring@{c c c})
                (RMod_Cocartesian_via_GAFT Int_Ring)
                (Ring_RMod Int_Ring) (Ring_RMod Int_Ring))),
     a0 ≈ b0) → False.
Proof.
  intro Hall.
  apply int_one_neq_zero.
  apply (RMod_inl_via_GAFT_injective (Ring_RMod Int_Ring) (Ring_RMod Int_Ring)).
  apply Hall.
Qed.
