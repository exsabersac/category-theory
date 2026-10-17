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
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.AFT.

Generalizable All Variables.

(* * * Colimits rings, adjoint 函子 定理 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Ring
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings
 Wikipedia: https://en.wikipedia.org/wiki/Free_product_of_associative_algebras

   本文件给出余极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The solution set at a diagram *)

Section RngDiagonalSolutionSet.

Context {J : Category}.
Context (D : J ⟶ Rng).

(* 相关说明。 （已译） *)
Definition RGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (rig_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition RGenAb : AbObject := FreeAbObject RGen.

Definition rins (j : J) (a : carrier (rig_setoid (D j))) : FRTerm RGenAb :=
  @fr_gen RGenAb (@fa_gen RGen (j; a)).

(* 相关说明。 （已译） *)
Record IsRngCoconeCong (Rq : FRTerm RGenAb → FRTerm RGenAb → Prop) : Prop := {
  rcc_rng  : IsRngCongruence Rq;
  rcc_resp : ∀ j a b, a ≈ b → Rq (rins j a) (rins j b);
  rcc_zero : ∀ j, Rq (rins j (rig_zero (D j))) (@fr_zero RGenAb);
  rcc_add  : ∀ j a b, Rq (rins j (rig_add (D j) a b))
                         (@fr_plus RGenAb (rins j a) (rins j b));
  rcc_one  : ∀ j, Rq (rins j (rig_one (D j))) (@fr_one RGenAb);
  rcc_mul  : ∀ j a b, Rq (rins j (rig_mul (D j) a b))
                         (@fr_mul RGenAb (rins j a) (rins j b));
  rcc_nat  : ∀ j k (f : j ~{J}~> k) a,
               Rq (rins k (rig_map (fmap[D] f) a)) (rins j a)
}.

Definition RDCongIdx : Type :=
  { Rq : FRTerm RGenAb → FRTerm RGenAb → Prop & IsRngCoconeCong Rq }.

Definition RDQ (i : RDCongIdx) : obj[Rng] := QRng (`1 i) (rcc_rng _ (`2 i)).

Definition rdq_leg (i : RDCongIdx) (j : J) : D j ~{Rng}~> RDQ i.
Proof.
  unshelve refine (@Build_RigHom (D j) (RDQ i)
                     {| morphism := rins j |} _ _ _ _).
  - intros a b Hab; exact (rcc_resp _ (`2 i) j a b Hab).
  - exact (rcc_zero _ (`2 i) j).
  - intros a b; exact (rcc_add _ (`2 i) j a b).
  - exact (rcc_one _ (`2 i) j).
  - intros a b; exact (rcc_mul _ (`2 i) j a b).
Defined.

Definition rdq_arr (i : RDCongIdx) :
  D ~{[J, Rng]}~> fobj[@Diagonal Rng J] (RDQ i).
Proof.
  unshelve refine (@Build_Transform' J Rng D (fobj[@Diagonal Rng J] (RDQ i))
                     (fun j => rdq_leg i j) _).
  intros j k f a; simpl.
  apply (rc_sym _ _ (rcc_rng _ (`2 i))).
  exact (rcc_nat _ (`2 i) j k f a).
Defined.

(* 相关说明。 （已译） *)
Section Cover.

Context (c : Rng) (h : D ~{[J, Rng]}~> fobj[@Diagonal Rng J] c).

Definition rflat : RGen ~{Sets}~> Ab_Forget (Rng_Forget_Ab c).
Proof using h.
  unshelve refine {| morphism := fun p => rig_map (transform[h] (`1 p)) (`2 p) |}.
  intros p q Hpq; simpl in Hpq; subst; reflexivity.
Defined.

Definition rhab : RGenAb ~{Ab}~> Rng_Forget_Ab c :=
  @free_ab_extend RGen (Rng_Forget_Ab c) rflat.

(* Transparent on purpose: see the header. *)
Lemma rker_cocone : IsRngCoconeCong (rng_ker rhab).
Proof using h.
  constructor.
  - exact (rng_ker_is_cong rhab).
  - intros j a b Hab; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    now rewrite Hab.
  - intros j; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_zero (transform[h] j)).
  - intros j a b; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_add (transform[h] j)).
  - intros j; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_one (transform[h] j)).
  - intros j a b; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    apply (rig_map_mul (transform[h] j)).
  - intros j k f a; unfold rng_ker; apply (@pequiv_from _ _ (rig_prop c)); simpl.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition rker_idx : RDCongIdx := (rng_ker rhab; rker_cocone).

End Cover.

Definition Diagonal_Rng_solution_set : SolutionSet (@Diagonal Rng J) D.
Proof.
  unshelve refine (@Build_SolutionSet Rng ([J, Rng]) (@Diagonal Rng J) D
                     RDCongIdx RDQ rdq_arr _).
  intros c h.
  exists (rker_idx c h).
  exists (rng_ker_med (rhab c h)).
  intros j a; simpl.
  reflexivity.
Defined.

End RngDiagonalSolutionSet.

(* 相关说明。 （已译） *)

Definition Rng_colim_via_GAFT (J : Category) :
  { K : [J, Rng] ⟶ Rng & K ⊣ @Diagonal Rng J } :=
  GAFT (@Diagonal Rng J) Rng_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_Rng_solution_set J).

Definition Rng_Cocomplete_via_GAFT : @Cocomplete Rng :=
  fun J F => Diagonal_left_adjoint_HasColimits (projT2 (Rng_colim_via_GAFT J)) F.

(* 相关说明。 （已译） *)

Definition Rng_FinitelyCocomplete_via_GAFT : @FinitelyCocomplete Rng :=
  Cocomplete_FinitelyCocomplete Rng_Cocomplete_via_GAFT.

(* Mac Lane §V.7 Exercise 2. *)
Definition Rng_Cocartesian_via_GAFT : @Cocartesian Rng :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op Rng_FinitelyCocomplete_via_GAFT).

Definition Rng_HasCoequalizers_via_GAFT : HasCoequalizers Rng :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op Rng_FinitelyCocomplete_via_GAFT)).

Definition Rng_Initial_via_GAFT : @Initial Rng :=
  FinitelyCocomplete_Initial Rng_FinitelyCocomplete_via_GAFT.
