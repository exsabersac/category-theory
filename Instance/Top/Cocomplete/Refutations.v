Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Complete.Refutations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Cocompleteness of spaces refuted above the points *)

(*
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Cantor%27s+theorem

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** [PTopCat]: Freyd's form, dualized, and transported above the points *)

(* Freyd's form, dualized: an arrow index at the shape universe refutes
   cocompleteness there. *)
Theorem PTop_not_cocomplete_Freyd@{r s o so +| o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (freyd_no_separated_pair (ArrowIndex_op AI)
           (a:=PBool) (b:=PPoint) ppoint_true ppoint_false _ _
           (complete_iprod (Complete_op_of_Cocomplete cocomp)
              (fun _ : ai_index (ArrowIndex_op AI) => PPoint))
           (fun h => pmap h ttt) (fun u v H => H ttt) eq_refl eq_refl).
Qed.

(* Every shape universe strictly above the points, under decidable
   equality of spaces: the canonical index is built at [PTopCat@{o s}]
   and transported by Instance/Top/Complete/Refutations.v's
   [PTop_ArrowIndex_transport], as the limit side does. *)
Theorem PTop_not_cocomplete_ObjDecEq@{r s o so +| o < so, o < s +}
  (DE : ObjDecEq PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_Freyd
           (PTop_ArrowIndex_transport@{s o s so}
              (canonical_ArrowIndex (DE : ObjDecEq PTopCat@{o s})))
           cocomp).
Qed.

Theorem PTop_not_cocomplete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_ObjDecEq (ObjDecEq_of_IEM E PTopCat@{o so})
           cocomp).
Qed.

(* Through the recipe, the same boundary for the points: were [Sets]
   cocomplete at a shape universe above its carriers, Instance/Top/
   Cocomplete.v's [PTop_Colimit_lift] would make [PTopCat] cocomplete
   there. *)
Theorem Sets_not_cocomplete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} Sets@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_IEM E
           (fun D F => PTop_Colimit_lift F (cocomp D (PForget ◯ F)))).
Qed.

(** ** The Type-valued [Top]: Freyd's form, and transported below the homs *)

(* Freyd's form, the exact dual of Instance/Top/StoneCech/Refutations.v's
   [Top_not_complete]. *)
Theorem Top_not_cocomplete_Freyd@{r s h o +}
  (AI : ArrowIndex@{s h h} Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (freyd_no_separated_pair (ArrowIndex_op AI)
           (a:=Bool_Discrete) (b:=Point_Top)
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (complete_iprod (Complete_op_of_Cocomplete cocomp)
              (fun _ : ai_index (ArrowIndex_op AI) => Point_Top))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(* Every shape universe strictly above the points, the shapes below the
   homs included, under decidable equality of spaces: the canonical index
   is built at [Top@{s o}] and transported by Instance/Top/Complete/
   Refutations.v's [Top_ArrowIndex_transport], as the limit side does. *)
Theorem Top_not_cocomplete_ObjDecEq@{r s h o +| o < h, o < s +}
  (DE : ObjDecEq Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_cocomplete_Freyd
           (Top_ArrowIndex_transport@{s o s h}
              (canonical_ArrowIndex (DE : ObjDecEq Top@{s o})))
           cocomp).
Qed.

Theorem Top_not_cocomplete_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_cocomplete_ObjDecEq (ObjDecEq_of_IEM E Top@{h o}) cocomp).
Qed.

(** ** A second argument: Cantor's diagonal at the points of one coproduct *)

(* No map from the predicates on a type into it is injective up to a
   reflexive relation: the predicate "encodes a predicate it does not
   hold of" holds of its own code exactly when it does not. *)
Lemma cocomp_cantor_diagonal@{u} {A : Type@{u}} (R : A → A → Type@{u})
  (R_refl : ∀ a, R a a) (enc : (A → Prop) → A)
  (enc_inj : ∀ U V, R (enc U) (enc V) → U = V) : False.
Proof.
  pose (Dg := fun p : A => ex (fun U => inhabited (R (enc U) p) /\ ~ U p)).
  assert (N : ~ Dg (enc Dg)).
  { intros [U [[HU] nU]]. pose proof (enc_inj U Dg HU) as E.
    subst U. apply nU. exists Dg. split; [constructor; exact HU|exact nU]. }
  apply N. exists Dg. split; [constructor; exact (R_refl _)|exact N].
Qed.

(** ** [PTopCat]: Cantor at the points of one coproduct *)

(* The index of the coproduct: a space with a predicate on its points.  It
   quantifies over the spaces, so it sits strictly above the points. *)
Definition pcc_index@{o s | o < s +} : Type@{s} :=
  { X : PTop@{o} & pt_carrier X → Prop }.

Section PCantor.

Universes o so s r.
Constraint o < so.
Constraint o < s.

Context (DE : ObjDecEq PTopCat@{o so}).
Context (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}).

#[local] Notation K := (pcc_index@{o s}).

(* A space [Om] and a family of its points [c k0 k] that recognizes [k0]:
   [c k0 k] is equivalent to [c k0 k0] only at [k = k0]. *)
Context (Om : PTop@{o}) (c : K → K → pt_carrier Om).
Context (c_spec : ∀ k0 k, c k0 k ≈ c k0 k0 → k = k0).

Let CC := Complete_op_of_Cocomplete cocomp.

(* The coproduct of [pcc_index]-many points, which cocompleteness at [s]
   supplies. *)
Definition pcc_sum : PTop@{o} :=
  complete_iprod_obj CC (fun _ : K => PPoint@{o}).

Definition pcc_inj (k : K) : PPoint@{o} ~{PTopCat@{o so}}~> pcc_sum :=
  complete_iprod_proj CC (fun _ : K => PPoint@{o}) k.

Definition pcc_leg (k0 k : K) : PPoint@{o} ~{PTopCat@{o so}}~> Om :=
  pdisc_mor unit_setoid_object Om (pconst unit_setoid_object Om (c k0 k)).

(* The copairing of the legs at [k0]. *)
Definition pcc_sep (k0 : K) : pcc_sum ~{PTopCat@{o so}}~> Om :=
  unique_obj (iprod_desc (complete_iprod CC (fun _ : K => PPoint@{o}))
                (c:=Om) (pcc_leg k0)).

Lemma pcc_sep_at (k0 k : K) :
  pmap (pcc_sep k0) (pmap (pcc_inj k) ttt) ≈ c k0 k.
Proof.
  exact (unique_property
           (iprod_desc (complete_iprod CC (fun _ : K => PPoint@{o}))
              (c:=Om) (pcc_leg k0)) k ttt).
Qed.

(* A predicate on the points of the coproduct encodes to the point of its
   own summand. *)
Definition pcc_enc (U : pt_carrier pcc_sum → Prop) : pt_carrier pcc_sum :=
  pmap (pcc_inj (existT _ pcc_sum U)) ttt.

Lemma pcc_enc_inj (U V : pt_carrier pcc_sum → Prop) :
  pcc_enc U ≈ pcc_enc V → U = V.
Proof using All.
  intro H.
  pose proof (proper_morphism (pmap (pcc_sep (existT _ pcc_sum U))) _ _ H)
    as H1.
  assert (E : existT (fun X : PTop@{o} => pt_carrier X → Prop) pcc_sum V
              = existT _ pcc_sum U).
  { apply c_spec.
    transitivity (pmap (pcc_sep (existT _ pcc_sum U)) (pcc_enc V));
      [symmetry; exact (pcc_sep_at _ _)|].
    transitivity (pmap (pcc_sep (existT _ pcc_sum U)) (pcc_enc U));
      [symmetry; exact H1|exact (pcc_sep_at _ _)]. }
  symmetry. exact (inj_pair2_eq_dec _ DE _ _ _ _ E).
Qed.

Lemma pcc_contradiction : False.
Proof using All.
  exact (cocomp_cantor_diagonal (@equiv _ (pt_carrier pcc_sum))
           (fun p => reflexivity p) pcc_enc pcc_enc_inj).
Qed.

End PCantor.

(* The truth values, under [<->], as a setoid at the points' universe. *)
Program Definition pcc_Prop@{o | Set < o} : SetoidObject@{o o} := {|
  carrier := Prop;
  is_setoid := {| equiv := fun P Q => P <-> Q |}
|}.
Next Obligation.
  constructor.
  - intro P; exact (iff_refl P).
  - intros P Q H; exact (iff_sym H).
  - intros P Q R H1 H2; exact (iff_trans H1 H2).
Qed.

(* Cocompleteness of [PTopCat] is refuted at every shape universe strictly
   above the points, under decidable equality of spaces: the separator is
   the discrete space of truth values. *)
Theorem PTop_not_cocomplete_Cantor_ObjDecEq@{r s o so +| o < so, o < s,
                                               Set < o +}
  (DE : ObjDecEq PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  apply (pcc_contradiction DE cocomp (PDiscrete pcc_Prop@{o})
           (fun k0 k => k = k0)).
  intros k0 k H. exact (proj2 H eq_refl).
Qed.

(* The same under informative excluded middle, with [PBool] as the
   separator, so that no [Set < o] is needed. *)
Theorem PTop_not_cocomplete_Cantor_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  apply (pcc_contradiction
           (fun x y => match E (x = y) with
                       | inl e => left e
                       | inr n => right n
                       end) cocomp PBool@{o}
           (fun k0 k => match E (k = k0) with
                        | inl _ => true
                        | inr _ => false
                        end)).
  intros k0 k H. simpl in H.
  destruct (E (k = k0)) as [e|n]; [exact e|].
  destruct (E (k0 = k0)) as [_|n0]; [discriminate H|].
  destruct (n0 eq_refl).
Qed.

(** ** The Type-valued [Top]: Cantor's argument *)

Definition tcc_index@{o s | o < s +} : Type@{s} :=
  { X : TopSpace@{o} & top_carrier X → Prop }.

Section TCantor.

Universes o h s r.
Constraint o < h.
Constraint o < s.

Context (DE : ObjDecEq Top@{h o}).
Context (cocomp : @Cocomplete@{r s h h} Top@{h o}).

#[local] Notation K := (tcc_index@{o s}).

Context (Om : TopSpace@{o}) (c : K → K → top_carrier Om).
Context (c_spec : ∀ k0 k, c k0 k ≈ c k0 k0 → k = k0).

Let CC := Complete_op_of_Cocomplete cocomp.

Definition tcc_sum : TopSpace@{o} :=
  complete_iprod_obj CC (fun _ : K => Point_Top).

Definition tcc_inj (k : K) : Point_Top ~{Top@{h o}}~> tcc_sum :=
  complete_iprod_proj CC (fun _ : K => Point_Top) k.

Definition tcc_leg (k0 k : K) : Point_Top ~{Top@{h o}}~> Om :=
  top_point Om (c k0 k).

Definition tcc_sep (k0 : K) : tcc_sum ~{Top@{h o}}~> Om :=
  unique_obj (iprod_desc (complete_iprod CC (fun _ : K => Point_Top))
                (c:=Om) (tcc_leg k0)).

Lemma tcc_sep_at (k0 k : K) :
  continuous_map (tcc_sep k0) (continuous_map (tcc_inj k) ttt) ≈ c k0 k.
Proof.
  exact (unique_property
           (iprod_desc (complete_iprod CC (fun _ : K => Point_Top))
              (c:=Om) (tcc_leg k0)) k ttt).
Qed.

Definition tcc_enc (U : top_carrier tcc_sum → Prop) : top_carrier tcc_sum :=
  continuous_map (tcc_inj (existT _ tcc_sum U)) ttt.

Lemma tcc_enc_inj (U V : top_carrier tcc_sum → Prop) :
  tcc_enc U ≈ tcc_enc V → U = V.
Proof using All.
  intro H.
  pose proof (proper_morphism (continuous_map (tcc_sep (existT _ tcc_sum U)))
                _ _ H) as H1.
  assert (E : existT (fun X : TopSpace@{o} => top_carrier X → Prop) tcc_sum V
              = existT _ tcc_sum U).
  { apply c_spec.
    transitivity (continuous_map (tcc_sep (existT _ tcc_sum U)) (tcc_enc V));
      [symmetry; exact (tcc_sep_at _ _)|].
    transitivity (continuous_map (tcc_sep (existT _ tcc_sum U)) (tcc_enc U));
      [symmetry; exact H1|exact (tcc_sep_at _ _)]. }
  symmetry. exact (inj_pair2_eq_dec _ DE _ _ _ _ E).
Qed.

Lemma tcc_contradiction : False.
Proof using All.
  exact (cocomp_cantor_diagonal (@equiv _ (top_carrier tcc_sum))
           (fun p => reflexivity p) tcc_enc tcc_enc_inj).
Qed.

End TCantor.

Theorem Top_not_cocomplete_Cantor_ObjDecEq@{r s h o +| o < h, o < s,
                                              Set < o +}
  (DE : ObjDecEq Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  apply (tcc_contradiction DE cocomp (Discrete_Top pcc_Prop@{o})
           (fun k0 k => k = k0)).
  intros k0 k H. exact (proj2 H eq_refl).
Qed.

Theorem Top_not_cocomplete_Cantor_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  apply (tcc_contradiction
           (fun x y => match E (x = y) with
                       | inl e => left e
                       | inr n => right n
                       end) cocomp Bool_Discrete
           (fun k0 k => match E (k = k0) with
                        | inl _ => true
                        | inr _ => false
                        end)).
  intros k0 k H. simpl in H.
  destruct (E (k = k0)) as [e|n]; [exact e|].
  destruct (E (k0 = k0)) as [_|n0]; [discriminate H|].
  destruct (n0 eq_refl).
Qed.
