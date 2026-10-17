Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/subobject
 Wikipedia: https://en.wikipedia.org/wiki/Subobject

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsWellPoweredUp.

Universe o so.
Constraint o < so.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition sets_pred_index (X : SetoidObject@{o o}) :=
  { P : carrier X → Type@{o} & ∀ a b : carrier X, a ≈ b → P a → P b }.

(* 相关说明。 （已译） *)
Definition sets_pred_setoid (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  SetoidObject@{o o}.
Proof.
  unshelve refine
    {| carrier := { a : carrier X & `1 P a } ;
       is_setoid := {| equiv := fun p q =>
                         @equiv _ (is_setoid X) (`1 p) (`1 q) |} |}.
  constructor.
  - intro p; reflexivity.
  - intros p q H; symmetry; exact H.
  - intros p q r H1 H2; etransitivity; [exact H1|exact H2].
Defined.

Definition sets_pred_incl (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  sets_pred_setoid X P ~{Sets@{o so}}~> X.
Proof.
  unshelve refine {| morphism := fun p => `1 p |}.
  intros p q H; exact H.
Defined.

Lemma sets_pred_incl_monic (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  @Monic Sets@{o so} _ _ (sets_pred_incl X P).
Proof.
  apply (fst (injectivity_is_monic (sets_pred_incl X P))).
  intros p q H; exact H.
Qed.

Definition sets_sub_of_pred (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  @SubObj Sets@{o so} X :=
  @Build_SubObj Sets@{o so} X (sets_pred_setoid X P) (sets_pred_incl X P)
    (sets_pred_incl_monic X P).

(* 相关说明。 （已译） *)
Definition sets_pred_of_sub (X : SetoidObject@{o o})
  (u : @SubObj Sets@{o so} X) : sets_pred_index X.
Proof.
  exists (fun b => { a : carrier (sub_dom u) & sub_mono u a ≈ b }).
  intros b b' Hb [a Ha]; exists a; etransitivity; [exact Ha|exact Hb].
Defined.

(* The domain 同构. Forward: project carried preimage;
 it respects ≈ because mono injective. （已译） *)
Definition sets_pred_fwd (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  sets_pred_setoid X (sets_pred_of_sub X u) ~{Sets@{o so}}~> sub_dom u.
Proof.
  pose proof (snd (injectivity_is_monic (sub_mono u)) (sub_is_monic u)) as inj.
  unshelve refine {| morphism := fun p => `1 (`2 p) |}.
  intros [b [a Ha]] [b' [a' Ha']] H; simpl in *.
  apply inj. rewrite Ha, Ha'. exact H.
Defined.

Definition sets_pred_bwd (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  sub_dom u ~{Sets@{o so}}~> sets_pred_setoid X (sets_pred_of_sub X u).
Proof.
  unshelve refine {| morphism := fun a =>
      existT (fun b => { a' : carrier (sub_dom u) &
                         @equiv _ (is_setoid X) (sub_mono u a') b })
             (sub_mono u a)
             (existT (fun a' => @equiv _ (is_setoid X) (sub_mono u a')
                                                     (sub_mono u a)) a
                     (@Equivalence_Reflexive _ _ (@setoid_equiv _ (is_setoid X))
                        (sub_mono u a))) |}.
  intros a a' H; simpl. apply proper_morphism; exact H.
Defined.

Definition sets_pred_iso (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  @Isomorphism Sets@{o so} (sets_pred_setoid X (sets_pred_of_sub X u))
    (sub_dom u).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} _ _ (sets_pred_fwd X u) (sets_pred_bwd X u)
       _ _).
  - intro a; simpl; reflexivity.
  - intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition sets_pred_to_from (X : SetoidObject@{o o})
  (u : @SubObj Sets@{o so} X) :
  sets_sub_of_pred X (sets_pred_of_sub X u) ≈ u.
Proof.
  exists (sets_pred_iso X u).
  intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition Sets_WellPoweredAt_up (X : SetoidObject@{o o}) :
  @WellPoweredAt Sets@{o so} X :=
  {| wp_index   := sets_pred_index X ;
     wp_to      := sets_sub_of_pred X ;
     wp_from    := sets_pred_of_sub X ;
     wp_to_from := sets_pred_to_from X |}.

(* 相关说明。 （已译） *)

(* The index at [X]: [Type@{o}]-valued 等价 relations the
 carrier coarser than ≈. It lives at [o+1]. （已译） *)
Definition sets_rel_index (X : SetoidObject@{o o}) :=
  { R : crelation@{o o} (carrier X) & (Equivalence R * SetoidCoarser R)%type }.

Definition sets_quot_of_rel (X : SetoidObject@{o o}) (R : sets_rel_index X) :
  @QuotObj Sets@{o so} X :=
  SetsQuotient_QuotObj X (`1 R) (fst (`2 R)) (snd (`2 R)).

(* The 核 relation quotient's epimorphism. Written tactic
 form: anonymous pair whose expected type needs unfolding
 [sets_rel_index] down carrier is known Coq 8.19/8.20 trap.（已译） *)
Definition sets_rel_of_quot (X : SetoidObject@{o o})
  (q : @QuotObj Sets@{o so} X) : sets_rel_index X.
Proof.
  exists (sets_coimage_rel (quot_epi q)).
  exact (sets_coimage_rel_Equivalence (quot_epi q),
         sets_coimage_rel_coarser (quot_epi q)).
Defined.

Definition sets_rel_fwd (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q))
    ~{Sets@{o so}}~> quot_cod q.
Proof.
  unshelve refine {| morphism := fun a => quot_epi q a |}.
  intros a b H; exact H.
Defined.

(* Backward: the preimage [Sets_quot_epi_surjective] returns is DATA,
   because [∃] is [sigT] here. *)
Definition sets_rel_bwd (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  quot_cod q
    ~{Sets@{o so}}~> quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q)).
Proof.
  unshelve refine {| morphism := fun b => `1 (Sets_quot_epi_surjective q b) |}.
  intros b b' H; simpl; unfold sets_coimage_rel.
  rewrite (`2 (Sets_quot_epi_surjective q b)),
          (`2 (Sets_quot_epi_surjective q b')).
  exact H.
Defined.

Definition sets_rel_iso (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  @Isomorphism Sets@{o so}
    (quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q))) (quot_cod q).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} _ _ (sets_rel_fwd X q) (sets_rel_bwd X q)
       _ _).
  - intro b; simpl. exact (`2 (Sets_quot_epi_surjective q b)).
  - intro a; simpl; unfold sets_coimage_rel.
    exact (`2 (Sets_quot_epi_surjective q (quot_epi q a))).
Defined.

Definition sets_rel_to_from (X : SetoidObject@{o o})
  (q : @QuotObj Sets@{o so} X) :
  sets_quot_of_rel X (sets_rel_of_quot X q) ≈ q.
Proof.
  apply (snd (quot_equiv_iff_iso _ _)).
  exists (sets_rel_iso X q).
  intro a; simpl; reflexivity.
Defined.

Definition Sets_CoWellPoweredAt_up (X : SetoidObject@{o o}) :
  @WellPoweredAt (Sets@{o so}^op) X :=
  {| wp_index   := sets_rel_index X ;
     wp_to      := sets_quot_of_rel X ;
     wp_from    := sets_rel_of_quot X ;
     wp_to_from := sets_rel_to_from X |}.

End SetsWellPoweredUp.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Sets_WellPoweredAt_up_carrier (X : SetoidObject)
  (P : sets_pred_index X) :
  carrier (sub_dom (wp_to (Sets_WellPoweredAt_up X) P))
    = { a : carrier X & `1 P a } := eq_refl.

(* 相关说明。 （已译） *)

Section SetsWellPoweredPinned.

Universe o so.
Constraint o < so.
Constraint Set < o.

Context (U : Untruncate@{o}).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_WellPoweredAt_untruncate (X : SetoidObject@{o o}) :
  @WellPoweredAt Sets@{o so} X :=
  @wp_of_classifier Sets@{o so} Sets_Terminal@{so o} Sets_HasPullbacks@{so o}
    (Sets_Classifier@{o so} U) X.

End SetsWellPoweredPinned.

Example Sets_WellPoweredAt_untruncate_index (U : Untruncate)
  (X : SetoidObject) :
  wp_index (Sets_WellPoweredAt_untruncate U X)
    = (X ~{Sets}~> Powerset_Omega) := eq_refl.

Definition Sets_WellPowered_untruncate@{o so t | o < so, Set < o, o < t +}
  (U : Untruncate@{o}) : WellPowered@{so o o so t} Sets@{o so} :=
  fun X => Sets_WellPoweredAt_untruncate U X.

(* 相关说明。 （已译） *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsIntersection.

Universe o so.
Constraint o < so.
Constraint Set < o.

Context (U : Untruncate@{o}) (X : SetoidObject@{o o}).
Context (P : @SubObj Sets@{o so} X → Type@{o}).
Context (HP : ∀ m m' : @SubObj Sets@{o so} X, m ≈ m' → P m → P m').

Definition sets_wp_family :
  option { i : wp_index (Sets_WellPoweredAt_untruncate U X)
         & P (wp_to (Sets_WellPoweredAt_untruncate U X) i) } →
  @SubObj Sets@{o so} X :=
  fun j => match j with
           | None => @sub_top Sets@{o so} X
           | Some p => wp_to (Sets_WellPoweredAt_untruncate U X) (`1 p)
           end.

Definition Sets_wellpowered_intersection :
  { w : @SubObj Sets@{o so} X &
    IsIntersection (fun k : { m : @SubObj Sets@{o so} X & P m } => `1 k) w }.
Proof using U HP.
  set (W := Sets_WellPoweredAt_untruncate U X).
  exists (@sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _
            None sets_wp_family).
  pose proof (@sub_intersection_IsIntersection Sets@{o so}
                Sets_HasWidePullbacks@{o so} X _ None sets_wp_family) as H.
  constructor.
  - intros [m pm].
    pose (p := HP m _ (symmetry (wp_to_from W m)) pm).
    apply (sub_le_trans _ (sets_wp_family (Some (wp_from W m; p)))).
    + exact (inter_le _ _ H (Some (wp_from W m; p))).
    + exact (sub_le_of_equiv _ _ (wp_to_from W m)).
  - intros v Hv.
    apply (inter_greatest _ _ H).
    intros [[i pi]|]; simpl.
    + exact (Hv (wp_to W i; pi)).
    + exact (sub_top_greatest v).
Defined.

End SetsIntersection.

(* 相关说明。 （已译） *)
Definition sets_sub_bot@{o so | o < so +} (X : SetoidObject@{o o}) :
  @SubObj Sets@{o so} X :=
  @Build_SubObj Sets@{o so} X _ _ (Sets_zero_monic X).

Lemma Sets_intersection_all_empty@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) (X : SetoidObject@{o o})
  (a : carrier (sub_dom (`1 (Sets_wellpowered_intersection U X
                               (fun _ => Datatypes.unit)
                               (fun _ _ _ t => t))))) : False.
Proof.
  destruct (inter_le _ _
              (`2 (Sets_wellpowered_intersection U X
                     (fun _ => Datatypes.unit) (fun _ _ _ t => t)))
              (sets_sub_bot X; tt)) as [k _].
  exact (match k a with end).
Qed.
