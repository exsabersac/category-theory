Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** * The free ring functors, read through the adjoint functor theorem *)

(*
 nLab: https://ncatlab.org/nlab/show/free+ring
 nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** * The factorization of [Rng_Forget] through [Ab] *)

(* On data these two functors are the same term.  The records are not
   convertible -- see the header -- which is why the two recones below
   exist at all. *)

Example rng_forget_factors_obj (R : Rng) :
  fobj[Rng_Forget] R = fobj[Ab_Forget ◯ Rng_Forget_Ab] R := eq_refl.

Example rng_forget_factors_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[Rng_Forget] f = fmap[Ab_Forget ◯ Rng_Forget_Ab] f := eq_refl.

(* [RngUnderlyingAb] (Instance/Rng/Free.v) IS that composite, so the
   same two readbacks hold against it.  These are what make the retyping of
   [free_ring_via_ab_adjunction] typecheck. *)

Example rng_underlying_ab_is_forget_obj (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[Rng_Forget] R := eq_refl.

Example rng_underlying_ab_is_forget_map (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[Rng_Forget] f := eq_refl.

(** * Continuity of [Rng_Forget_Ab], without a creation argument FOR IT,
      and without RAPL *)

Section RngAbContinuity.

Context {J : Category}.
Context (K : J ⟶ Rng).

(* A cone over [Ab_Forget ◯ (Rng_Forget_Ab ◯ K)] rebuilt as a cone over
   [Rng_Forget ◯ K].  Apex, legs and coherence proof are reused verbatim;
   only the diagram record changes, and every type the fields inhabit is
   convertible by the factorization above. *)
Definition rng_ab_recone (M : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)))
  : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Rng_Forget ◯ K)
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(* The other direction, needed for the reflection clause. *)
Definition rng_sets_recone (M : Cone (Rng_Forget ◯ K))
  : Cone (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) :=
  @Build_Cone J Sets (Ab_Forget ◯ (Rng_Forget_Ab ◯ K)) vertex_obj[M]
    (@Build_ACone J Sets vertex_obj[M] (Ab_Forget ◯ (Rng_Forget_Ab ◯ K))
       (fun j => cone_leg M j)
       (fun x y f => @cone_coherence J Sets _ _ (@coneFrom _ _ _ M) x y f)).

(* Step one: the image of a limiting cone of rings under [Ab_Forget ◯
   Rng_Forget_Ab] is limiting, because that composite's image cone IS
   [Rng_Forget]'s, and [Rng_Forget] is continuous.  Every cone the goal
   quantifies over is re-presented by [rng_ab_recone]; no tactic is
   involved. *)
Definition rng_ab_image_limit (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Ab_Forget (FCone Rng_Forget_Ab N)) :=
  fun M => Rng_Forget_continuous J K N HN (rng_ab_recone M).

(* Step two: [Ab_Forget] reflects limit cones, so the [Ab]-level cone is
   limiting.  This is where the bilinearity obstruction is bypassed -- the
   ring multiplication on the apex is never built over [Ab]. *)
Definition rng_ab_limit_cone (N : Cone K) (HN : IsLimitCone N) :
  IsLimitCone (FCone Rng_Forget_Ab N) :=
  Ab_Forget_reflects_limits (Rng_Forget_Ab ◯ K) (FCone Rng_Forget_Ab N)
    (rng_ab_image_limit N HN).

(* The same composite read backwards: [Ab_Forget] is continuous by
   creation ([Ab_Forget_creates_continuous], Instance/Ab/Limit.v, which
   presupposes no adjunction either), and [Rng_Forget] reflects. *)
Definition rng_ab_reflect (N : Cone K)
  (HN : IsLimitCone (FCone Rng_Forget_Ab N)) : IsLimitCone N :=
  Rng_Forget_reflects_limits K N
    (fun M =>
       Ab_Forget_creates_continuous J (Rng_Forget_Ab ◯ K)
         (FCone Rng_Forget_Ab N) HN (rng_sets_recone M)).

End RngAbContinuity.

(** The headline non-circular result. *)
Definition Rng_Forget_Ab_continuous : ContinuousFunctor Rng_Forget_Ab :=
  fun J K N HN => rng_ab_limit_cone K N HN.

Definition Rng_Forget_Ab_PreservesAllLimits :
  PreservesAllLimits Rng_Forget_Ab :=
  Continuous_PreservesAllLimits Rng_Forget_Ab_continuous.

Definition Rng_Forget_Ab_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget_Ab :=
  fun N HN => rng_ab_reflect K N HN.

(** * The underlying-set adjunction, retyped onto [Rng_Forget] *)

(* Instance/Rng/Free.v states the composite adjunction against
   [RngUnderlyingAb].  Every field of [Adjunction] mentions the right
   adjoint only through [U y] and [fmap[U] f], and the two readbacks above
   say those agree definitionally, so the five field types are convertible
   and the record copies across.  This is Instance/Rng/Free.v's own
   manoeuvre at the other pair of presentations.

   This is the first inhabitant in tree of [_ ⊣ Rng_Forget]: see the header
   for the measurement, and for why its absence was nominal. *)

Definition free_ring_via_ab_adjunction_set : free_ring_via_ab ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_ab Rng_Forget
    (@adj _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_ab_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_ab_adjunction).

(* The monoid route retyped the same way, so that the comparison below can
   be made against BOTH explicit constructions rather than only one. *)
Definition free_ring_via_mon_adjunction_set : free_ring_via_mon ⊣ Rng_Forget :=
  @Build_Adjunction Rng Sets free_ring_via_mon Rng_Forget
    (@adj _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction_ab)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction_ab).

(* The retyping is inert on the transpose, hence on the unit. *)
Example free_ring_via_ab_adjunction_set_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction_set X R) f
    = to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f := eq_refl.

(** * [Prop] congruences on the free-ring terms *)

(* THE NON-CIRCULAR SOLUTION SETS.

   A solution set for [Rng_Forget_Ab] at [A] must be a family of rings, at
   the universe the theorem demands, through which every homomorphism out
   of [A] factors.  The family used here is the QUOTIENTS OF THE FREE-RING
   TERM MODEL by [Prop]-valued congruences: [FRTerm A]
   (Instance/Rng/Free.v) with its relation [fr_eq], which is already a
   [Prop] inductive since the PR "algebraic carriers are sets"
   (2026-09-17).

   WHY THE INDEX IS THE RIGHT SIZE.  Every field of [IsRngCongruence] is a
   [Prop], so the record is a [Prop] and the sigma over it lands at the
   carrier universe rather than one above it.  Structure/Complete.v's SIZE
   NOTE, item 1, is the authority and is not restated; item 2(b) is why the
   index universe has to be the carrier universe in the first place.  The
   same device serves Instance/Mod/TensorAFT.v (section 3A) and
   Instance/Grp/FreeAFT.v.

   NO [PropEquiv] HYPOTHESIS ANYWHERE BELOW: [rig_prop] is a field of
   [RigObject] and [cmon_prop] a field of [CMonObject], both with
   [#[export] Existing Instance], so the kernel congruence of an evaluation
   is available at every ring with no side condition. *)

Section RngCongruence.

Context (A : AbObject).

Record IsRngCongruence (Rq : FRTerm A → FRTerm A → Prop) : Prop := {
  rc_refl  : ∀ s, Rq s s;
  rc_sym   : ∀ s t, Rq s t → Rq t s;
  rc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  rc_gen   : ∀ s t, fr_eq s t → Rq s t;
  rc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_plus A s t) (@fr_plus A s' t');
  rc_neg   : ∀ s s', Rq s s' → Rq (@fr_neg A s) (@fr_neg A s');
  rc_mul   : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (@fr_mul A s t) (@fr_mul A s' t')
}.

Definition RngCongIdx : Type :=
  { Rq : FRTerm A → FRTerm A → Prop & IsRngCongruence Rq }.

(* NAMED for [PropEquiv_of_relation]'s sake: written inline, its setoid
   argument is found by resolution, which picks the AMBIENT term setoid
   rather than the quotient's, and both implications are then refused. *)
Definition QRng_Setoid (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : Setoid (FRTerm A) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := rc_refl  Rq H
        ; Equivalence_Symmetric  := rc_sym   Rq H
        ; Equivalence_Transitive := rc_trans Rq H |} |}.

(* The quotient ring, at the SAME [Rng] instance.  Every law is the term
   model's own law passed through [rc_gen]. *)
Definition QRng (Rq : FRTerm A → FRTerm A → Prop) (H : IsRngCongruence Rq)
  : RingObject :=
  {| ring_rig := {|
       rig_setoid :=
         {| carrier := FRTerm A
          ; is_setoid := QRng_Setoid Rq H |};
       rig_zero := @fr_zero A;
       rig_add  := @fr_plus A;
       rig_one  := @fr_one A;
       rig_mul  := @fr_mul A;
       rig_add_respects := fun _ _ Hs _ _ Ht => rc_plus Rq H _ _ _ _ Hs Ht;
       rig_mul_respects := fun _ _ Hs _ _ Ht => rc_mul Rq H _ _ _ _ Hs Ht;
       rig_add_assoc := fun s t u => rc_gen Rq H _ _ (fre_add_assoc s t u);
       rig_add_comm := fun s t => rc_gen Rq H _ _ (fre_add_comm s t);
       rig_add_zero_l := fun s => rc_gen Rq H _ _ (fre_add_zero_l s);
       rig_mul_assoc := fun s t u => rc_gen Rq H _ _ (fre_mul_assoc s t u);
       rig_mul_one_l := fun s => rc_gen Rq H _ _ (fre_mul_one_l s);
       rig_mul_one_r := fun s => rc_gen Rq H _ _ (fre_mul_one_r s);
       rig_distr_l := fun s t u => rc_gen Rq H _ _ (fre_distr_l s t u);
       rig_distr_r := fun s t u => rc_gen Rq H _ _ (fre_distr_r s t u);
       rig_mul_zero_l := fun s => rc_gen Rq H _ _ (fr_mul_zero_l A s);
       rig_mul_zero_r := fun s => rc_gen Rq H _ _ (fr_mul_zero_r A s);
       rig_prop := @PropEquiv_of_relation _ (QRng_Setoid Rq H) Rq
                     (fun _ _ h => h) (fun _ _ h => h)
     |};
     ring_neg := @fr_neg A;
     ring_neg_respects := fun _ _ Hs => rc_neg Rq H _ _ Hs;
     ring_neg_l := fun s => rc_gen Rq H _ _ (fre_neg_l s)
  |}.

(* The canonical insertion of [A] into the quotient. *)
Definition QRng_insert (Rq : FRTerm A → FRTerm A → Prop)
  (H : IsRngCongruence Rq) : A ~{Ab}~> Rng_Forget_Ab (QRng Rq H).
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := @fr_gen A |}.
    intros a b Hab; exact (rc_gen Rq H _ _ (fre_gen Hab)).
  - exact (rc_gen Rq H _ _ (@fre_gen_zero A)).
  - intros a b; exact (rc_gen Rq H _ _ (fre_gen_plus a b)).
Defined.

End RngCongruence.

Arguments IsRngCongruence {A} Rq.
Arguments RngCongIdx A.
Arguments QRng_Setoid {A} Rq H.
Arguments QRng {A} Rq H.
Arguments QRng_insert {A} Rq H.

(* THE KERNEL CONGRUENCE of a ring-valued extension, and the covering. *)

Section RngKernel.

Context (A : AbObject).
Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Definition rng_ker : FRTerm A → FRTerm A → Prop :=
  fun s t => @pequiv _ _ (rig_prop R) (fr_eval h s) (fr_eval h t).

Lemma rng_ker_is_cong : IsRngCongruence rng_ker.
Proof.
  unfold rng_ker.
  constructor.
  - intro s; apply (@pequiv_from _ _ (rig_prop R)); reflexivity.
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R)); symmetry;
      exact (@pequiv_to _ _ (rig_prop R) _ _ Hst).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (rig_prop R)).
    transitivity (fr_eval h t);
      [ exact (@pequiv_to _ _ (rig_prop R) _ _ H1)
      | exact (@pequiv_to _ _ (rig_prop R) _ _ H2) ].
  (* [fr_eval_respects] takes [R] EXPLICITLY (Instance/Rng/Free.v)
     while [fr_eval] takes both implicitly. *)
  - intros s t Hst; apply (@pequiv_from _ _ (rig_prop R));
      exact (fr_eval_respects R h s t Hst).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_add_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
  - intros s s' H1; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (ring_neg_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (rig_prop R)); simpl.
    exact (rig_mul_respects R _ _ (@pequiv_to _ _ (rig_prop R) _ _ H1)
                              _ _ (@pequiv_to _ _ (rig_prop R) _ _ H2)).
Qed.

Definition rng_ker_idx : RngCongIdx A := existT _ rng_ker rng_ker_is_cong.

(* The mediator out of the quotient: respectfulness IS [pequiv_to]. *)
Program Definition rng_ker_med : QRng rng_ker rng_ker_is_cong ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval h |}
|}.
Solve All Obligations with
  (first [ (intros s t Hst; exact (@pequiv_to _ _ (rig_prop R) _ _ Hst))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. *)
Example rng_ker_factors (a : carrier (cmon_setoid A)) :
  rig_map rng_ker_med (cmon_map (QRng_insert rng_ker rng_ker_is_cong) a)
  = cmon_map h a
  := eq_refl.

End RngKernel.

Arguments rng_ker {A R} h.
Arguments rng_ker_is_cong {A R} h.
Arguments rng_ker_idx {A R} h.
Arguments rng_ker_med {A R} h.

(* NAMED so that both record fields elaborate [QRng] at ONE universe
   instance; written inline they mint two and the record is refused. *)
Definition QRngOf {A : Ab} (i : RngCongIdx A) : obj[Rng] :=
  QRng (`1 i) (`2 i).

Definition QRngInsertOf {A : Ab} (i : RngCongIdx A)
  : A ~{Ab}~> Rng_Forget_Ab (QRngOf i) := QRng_insert (`1 i) (`2 i).

Definition Rng_Forget_Ab_solution_set_prop (A : Ab) :
  SolutionSet Rng_Forget_Ab A.
Proof.
  unshelve refine (@Build_SolutionSet Rng Ab Rng_Forget_Ab A
                     (RngCongIdx A) QRngOf QRngInsertOf _).
  intros c h.
  exists (rng_ker_idx h), (rng_ker_med h).
  intro a; simpl; reflexivity.
Defined.

(* THE [Rng_Forget] HALF, TAKEN DIRECTLY AND NOT AS A COMPOSITE.

   The free ring on a SET is the free ring on the free abelian group on it
   ([free_ring_via_ab := FreeRngAb ◯ FreeAb], Instance/Rng/Free.v), so
   the SAME congruence index over [FreeAbObject X] and the SAME quotients
   serve; only the covering changes, by one transposition through
   [free_ab_extend].  Cost over the [Ab] case: three lines and no new
   vocabulary.

   THE COMPOSITE ROUTE WAS MEASURED AND NOT TAKEN.  Composing through
   Adjunction/Compose.v would need a GAFT application for [Ab_Forget] as
   well -- a fourth term model and a fourth congruence class -- or else
   would lean on the already-in-tree [free_ab_adjunction], which would make
   the result an adjunction-COMPOSITION rather than a GAFT application and
   leave [free_ring_via_GAFT] naming a theorem it did not prove.

   ONE TRAP: [free_ab_extend h] will not elaborate against an open [?A0]
   ([h : X ~> Rng_Forget c] and [X ~> Ab_Forget ?A0] are convertible but
   not unifiable), so the target is given explicitly. *)

Definition Rng_Forget_solution_set_prop (X : Sets) :
  SolutionSet Rng_Forget X.
Proof.
  unshelve refine (@Build_SolutionSet Rng Sets Rng_Forget X
                     (RngCongIdx (FreeAbObject X)) QRngOf
                     (fun i => fmap[Ab_Forget] (QRngInsertOf i)
                                 ∘ free_ab_unit X) _).
  intros c h.
  exists (rng_ker_idx (@free_ab_extend X (Rng_Forget_Ab c) h)),
         (rng_ker_med (@free_ab_extend X (Rng_Forget_Ab c) h)).
  intro a; simpl.
  reflexivity.
Defined.

(** * The two solution sets, and the two GAFT applications *)

(* THE CIRCULAR DISCHARGES, KEPT FOR COMPARISON; REMOVAL CANDIDATES FOR
   JOHN.  Each is named so that the circularity is visible at every use
   site rather than buried in a term: the family is the singleton at the
   unit of the adjunction the theorem is being asked to produce.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): these two are
   no longer what the GAFT applications below consume.  They are kept
   because removing working code is John's call, because the naming
   convention they establish is what makes the circularity legible, and
   because they are the honest comparison -- two different solution sets
   for one functor, one read off the answer and one not. *)

Definition Rng_Forget_Ab_solution_set_from_adjunction (A : Ab) :
  SolutionSet Rng_Forget_Ab A :=
  solution_set_of_adjunction free_rng_ab_adjunction A.

Definition Rng_Forget_solution_set_from_adjunction (X : Sets) :
  SolutionSet Rng_Forget X :=
  solution_set_of_adjunction free_ring_via_ab_adjunction_set X.

(* Mac Lane §V.6 Exercise 2, first half: the tensor/monoid ring on an
   abelian group.  [Continuous_PreservesImageLimit] is load-bearing -- see
   the header's measurement of what happens without it.

   NON-CIRCULAR since the PR "algebraic carriers are sets": the solution
   set is [Rng_Forget_Ab_solution_set_prop], built from the free-ring term
   model and its [Prop] congruences.  Strip Instance/Rng/Free.v's
   ADJUNCTIONS and this still stands; strip its TERM MODEL and it does
   not, which is the honest statement of what it depends on. *)
Definition free_rng_ab_via_GAFT : ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_prop.

(* Second half: the free ring on a set, likewise non-circular. *)
Definition free_ring_via_GAFT : ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_prop.

(* The circular readings, kept under names that say so. *)
Definition free_rng_ab_via_GAFT_from_adjunction :
  ∃ F : Ab ⟶ Rng, F ⊣ Rng_Forget_Ab :=
  GAFT Rng_Forget_Ab Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_Ab_continuous)
       Rng_Forget_Ab_solution_set_from_adjunction.

Definition free_ring_via_GAFT_from_adjunction :
  ∃ F : Sets ⟶ Rng, F ⊣ Rng_Forget :=
  GAFT Rng_Forget Rng_Complete
       (Continuous_PreservesImageLimit Rng_Forget_continuous)
       Rng_Forget_solution_set_from_adjunction.

(** * The comparison clauses, at [≈] *)

(* [GAFT] is [Qed], so its output does not reduce and no [eq_refl] is
   available; the header quotes the refusal.  What IS available is the
   uniqueness of left adjoints, and [left_adjoints_agree]
   (Instance/Rng/Free.v) is [Defined], so the comparison morphism has a
   name and the unit clause can be stated. *)

Definition free_rng_ab_via_GAFT_agrees : `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoints_agree (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction.

Definition free_ring_via_GAFT_agrees :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoints_agree (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set.

(* RECORDED STATEMENT CHANGE, PR "algebraic carriers are sets"
   (2026-09-17), AND THE MEASURED REASON.  This clause and the four other
   [_mon] ones below used to be stated about [free_ring_via_GAFT] and are
   now stated about [free_ring_via_GAFT_from_adjunction], the circular
   reading.  Nothing is lost -- the same theorem, "left adjoints to
   [Rng_Forget] agree", is still in tree against the monoid-ring route --
   but the WITNESS is a different constant and that must be said.

   THE OBSTRUCTION IS [free_ring_via_mon]'S OWN [Set] PIN, not the new
   solution set's fault and not repairable from this file.  Measured,
   [About] under [Set Printing Universes]:

     free_ring_via_mon@{u u0 … u7} : Functor@{u Set Set u …}
     free_ring_via_ab@{u u0 … u8}  : Functor@{u u1 u1 u0 …}

   -- the monoid route pins the hom AND proof universes of [Sets] to
   [Set], where the abelian-group route leaves them free.  The
   non-circular [free_ring_via_GAFT] carries the [Set < carrier] side
   condition of the [Prop] index (see the solution-set section above), so
   the two cannot be compared, and the attempt is refused with

     The term "free_ring_via_mon" has type "Sets@{Set u} ⟶ Rng@{u Set}"
     while it is expected to have type "Sets@{u0 u1} ⟶ Rng@{u1 u0}"
     (universe inconsistency: Cannot enforce Set = u0 because Set < u0)

   (generated universe names replaced positionally; everything else
   verbatim).  [free_ring_via_GAFT_agrees] above, against
   [free_ring_via_ab], is unaffected and IS about the non-circular
   constant.  Widening [free_ring_via_mon] would be a change to
   Instance/Rng/Free.v and belongs to its own commit, exactly as the
   widening of Adjunction/SpanningArrow.v did. *)
Definition free_ring_via_GAFT_agrees_mon :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoints_agree (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(* Theory/Adjunction.v's [left_adjoint_iso] inhabits the same three
   types.  The two terms are NOT identified -- that theorem is [Qed], so no
   component of it reduces and none can be named, which is exactly why the
   transparent donor is used above. *)

Example free_rng_ab_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_rng_ab_via_GAFT ≈ FreeRngAb :=
  left_adjoint_iso Rng_Forget_Ab _ FreeRngAb (`2 free_rng_ab_via_GAFT)
    free_rng_ab_adjunction.

Example free_ring_via_GAFT_agrees_via_left_adjoint_iso :
  `1 free_ring_via_GAFT ≈ free_ring_via_ab :=
  left_adjoint_iso Rng_Forget _ free_ring_via_ab (`2 free_ring_via_GAFT)
    free_ring_via_ab_adjunction_set.

Example free_ring_via_GAFT_agrees_mon_via_left_adjoint_iso :
  `1 free_ring_via_GAFT_from_adjunction ≈ free_ring_via_mon :=
  left_adjoint_iso Rng_Forget _ free_ring_via_mon
    (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set.

(** ** The comparison morphisms, named *)

Definition free_rng_ab_via_GAFT_comparison (A : Ab)
  : `1 free_rng_ab_via_GAFT A ~{Rng}~> FreeRngAb A :=
  adj_left_compare (`2 free_rng_ab_via_GAFT) free_rng_ab_adjunction A.

Definition free_ring_via_GAFT_comparison (X : Sets)
  : `1 free_ring_via_GAFT X ~{Rng}~> free_ring_via_ab X :=
  adj_left_compare (`2 free_ring_via_GAFT) free_ring_via_ab_adjunction_set X.

Definition free_ring_via_GAFT_comparison_mon (X : Sets)
  : `1 free_ring_via_GAFT_from_adjunction X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare (`2 free_ring_via_GAFT_from_adjunction)
    free_ring_via_mon_adjunction_set X.

(* [left_adjoints_agree] is [Defined], so each comparison IS the component
   of the corresponding natural isomorphism, by [eq_refl] and not by an
   argument. *)

Example free_rng_ab_via_GAFT_comparison_is_component (A : Ab) :
  to (projT1 free_rng_ab_via_GAFT_agrees A)
    = free_rng_ab_via_GAFT_comparison A := eq_refl.

Example free_ring_via_GAFT_comparison_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees X)
    = free_ring_via_GAFT_comparison X := eq_refl.

Example free_ring_via_GAFT_comparison_mon_is_component (X : Sets) :
  to (projT1 free_ring_via_GAFT_agrees_mon X)
    = free_ring_via_GAFT_comparison_mon X := eq_refl.

(** ** The unit clauses

    Mac Lane's exercise asks for the comparison to be compatible with the
    universal arrows, not merely for an isomorphism to exist.  Composing
    the comparison with the AFT-produced unit gives the explicit
    construction's own unit -- the ring-expression insertion on one side,
    the word insertion on the other. *)

Theorem free_rng_ab_via_GAFT_unit (A : Ab) :
  fmap[Rng_Forget_Ab] (free_rng_ab_via_GAFT_comparison A)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_rng_ab_via_GAFT) A
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.
Proof.
  exact (adj_left_compare_unit (`2 free_rng_ab_via_GAFT)
           free_rng_ab_adjunction A).
Qed.

Theorem free_ring_via_GAFT_unit (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ (`2 free_ring_via_GAFT) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT)
           free_ring_via_ab_adjunction_set X).
Qed.

Theorem free_ring_via_GAFT_unit_mon (X : Sets) :
  fmap[Rng_Forget] (free_ring_via_GAFT_comparison_mon X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        (`2 free_ring_via_GAFT_from_adjunction) X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_set X.
Proof.
  exact (adj_left_compare_unit (`2 free_ring_via_GAFT_from_adjunction)
           free_ring_via_mon_adjunction_set X).
Qed.
