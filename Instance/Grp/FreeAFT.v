Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.

Generalizable All Variables.

(** * The free group functor, read through the adjoint functor theorem *)

(*
 nLab: https://ncatlab.org/nlab/show/free+group

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** [Prop] congruences on the free group's carrier: a solution set AT
       the carrier universe *)

(* WHY THIS INDEX AND NOT A SIGMA OVER GROUPS.

   Mac Lane's family is indexed by SUBGROUPS of an arbitrary target, and a
   sigma over the objects of [Grp] sits strictly above [Grp]'s carriers,
   where the theorem cannot use it (Structure/Complete.v's SIZE NOTE is the
   authority and is not restated here).  What is built instead is a
   DIFFERENT index for the same job, the one Instance/Rng/AFT.v and
   Instance/Mod/TensorAFT.v also use: the [Prop]-valued congruences on the
   free group's word carrier [FGWord X].

   Every field of [IsGrpCongruence] is a [Prop], so the record is a [Prop]
   and the sigma over it lands AT the carrier universe rather than one
   above it.  Measured, [About] under [Set Printing Universes].  The
   criterion for what is quoted: every constraint relating the two argument
   universes to the index.  [FGCongIdx] binds thirteen universes; the other
   ten are [FGWord]'s and [IsGrpCongruence]'s and bound nothing here.

     FGCongIdx@{u u0 u1 …} : SetoidObject@{u u0} → Type@{u1}
     (* … Set < u1 / u <= u1 / u0 <= u1 / u0 = u … *)

   [u] is the generating setoid's carrier universe.  The bound on the index
   [u1] is [u <= u1] and NOT [u < u1], so [u1 := u] is expressible and the
   theorem accepts the family; that single inequality is the whole
   difference from a sigma over objects.

   [gc_gen] stores the free group's own equality as a PREMISE.  A [Π] into
   [Prop] is a [Prop] whatever the premise's sort, so nothing here depends
   on Instance/Grp/Free.v's [fg_equiv] being the truncation it now is: were
   that truncation reverted, this section would still be a [Prop].

   THE ONE SIDE CONDITION, stated and not smoothed over: [Set < carrier],
   the same one Instance/Mod/TensorAFT.v records.  [Set+1] is the sort
   of [Prop], so identifying the index universe with a carrier universe
   forces that carrier strictly above [Set].  Measured, the unconditional
   [Grp_Forget_solution_set_prop] carries [Set < u] on the solution set's
   index slot where the circular
   [Grp_Forget_solution_set_from_adjunction] does not.  In practice it
   costs nothing — Lib.v's [Unset Universe Minimization ToSet] keeps
   carrier universes off [Set] — but it is real, and it is pinned in
   Test/ProbeGrpFreeAFT442.v's section I. *)

Section FreeGrpCongruence.

Context (X : SetoidObject).

Record IsGrpCongruence (Rq : FGWord X → FGWord X → Prop) : Prop := {
  gc_refl  : ∀ w, Rq w w;
  gc_sym   : ∀ u v, Rq u v → Rq v u;
  gc_trans : ∀ u v w, Rq u v → Rq v w → Rq u w;
  gc_gen   : ∀ u v, @equiv _ (is_setoid (FreeGrpSetoid X)) u v → Rq u v;
  gc_mul   : ∀ u u' v v', Rq u u' → Rq v v' →
               Rq (grp_mul (FreeGrpObject X) u v)
                  (grp_mul (FreeGrpObject X) u' v');
  gc_inv   : ∀ u v, Rq u v →
               Rq (grp_inv (FreeGrpObject X) u) (grp_inv (FreeGrpObject X) v)
}.

Definition FGCongIdx : Type :=
  { Rq : FGWord X → FGWord X → Prop & IsGrpCongruence Rq }.

(* NAMED, or [PropEquiv_of_relation] picks the ambient setoid by resolution
   and both implications are refused. *)
Definition QGrp_Setoid (Rq : FGWord X → FGWord X → Prop)
  (H : IsGrpCongruence Rq) : Setoid (FGWord X) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := gc_refl  Rq H
        ; Equivalence_Symmetric  := gc_sym   Rq H
        ; Equivalence_Transitive := gc_trans Rq H |} |}.

(* The quotient group, at the SAME [Grp] universe instance as the ambient
   groups.  Every law is the free group's own law passed through [gc_gen],
   and [grp_prop] is the congruence itself — the carrier is a set because
   the relation indexing it is already [Prop]-valued. *)
Definition QGrp (Rq : FGWord X → FGWord X → Prop)
  (H : IsGrpCongruence Rq) : GrpObject :=
  {| grp_setoid := {| carrier := FGWord X ; is_setoid := QGrp_Setoid Rq H |};
     grp_unit := grp_unit (FreeGrpObject X);
     grp_mul  := grp_mul (FreeGrpObject X);
     grp_inv  := grp_inv (FreeGrpObject X);
     grp_mul_respects := fun _ _ Hu _ _ Hv => gc_mul Rq H _ _ _ _ Hu Hv;
     grp_mul_assoc := fun a b c =>
       gc_gen Rq H _ _ (grp_mul_assoc (FreeGrpObject X) a b c);
     grp_mul_unit_l := fun a =>
       gc_gen Rq H _ _ (grp_mul_unit_l (FreeGrpObject X) a);
     grp_mul_inv_l := fun a =>
       gc_gen Rq H _ _ (grp_mul_inv_l (FreeGrpObject X) a);
     grp_prop := @PropEquiv_of_relation _ (QGrp_Setoid Rq H) Rq
                   (fun _ _ h => h) (fun _ _ h => h)
  |}.

(* The insertion of generators into the quotient.  Written as a TACTIC
   proof: the record field expects `≈`, which is [Rq] only after delta. *)
Definition QGrp_insert (Rq : FGWord X → FGWord X → Prop)
  (H : IsGrpCongruence Rq) : X ~{Sets}~> Grp_Forget (QGrp Rq H).
Proof.
  unshelve refine {| morphism := fun a => fg_insert X a |}.
  intros a b Hab.
  exact (gc_gen Rq H _ _ (proper_morphism (fg_insert X) a b Hab)).
Defined.

End FreeGrpCongruence.

Arguments IsGrpCongruence {X} Rq.
Arguments QGrp_Setoid {X} Rq H.
Arguments QGrp {X} Rq H.
Arguments QGrp_insert {X} Rq H.

(** ** The kernel congruence of an extension

    The covering, and the one place the Grp phase of this PR is
    load-bearing.  [fg_ker] is the kernel of [free_grp_extend h] read as a
    relation on words, and it is a [Prop] because the TARGET group carries
    [grp_prop] as a field of [GrpObject] — no hypothesis on [G] and none on
    [X].  Before that field existed, the kernel of a homomorphism was a
    [crelation] and this index could not be written. *)

Section FreeGrpKernel.

Context (X : SetoidObject).
Context (G : GrpObject).
Context (h : X ~{Sets}~> Grp_Forget G).

Definition fg_ev (w : FGWord X) : carrier (grp_setoid G) :=
  grp_map (free_grp_extend h) w.

Definition fg_ker : FGWord X → FGWord X → Prop :=
  fun u v => @pequiv _ _ (grp_prop G) (fg_ev u) (fg_ev v).

Lemma fg_ker_is_cong : IsGrpCongruence fg_ker.
Proof.
  unfold fg_ker, fg_ev.
  constructor.
  - intro w; apply (@pequiv_from _ _ (grp_prop G)); reflexivity.
  - intros u v Huv; apply (@pequiv_from _ _ (grp_prop G)); symmetry;
      exact (@pequiv_to _ _ (grp_prop G) _ _ Huv).
  - intros u v w H1 H2; apply (@pequiv_from _ _ (grp_prop G)).
    transitivity (grp_map (free_grp_extend h) v);
      [ exact (@pequiv_to _ _ (grp_prop G) _ _ H1)
      | exact (@pequiv_to _ _ (grp_prop G) _ _ H2) ].
  - intros u v Huv; apply (@pequiv_from _ _ (grp_prop G)).
    exact (proper_morphism (grp_map (free_grp_extend h)) u v Huv).
  - intros u u' v v' H1 H2; apply (@pequiv_from _ _ (grp_prop G)).
    rewrite (grp_map_mul (free_grp_extend h) u v).
    rewrite (grp_map_mul (free_grp_extend h) u' v').
    exact (grp_mul_respects G _ _ (@pequiv_to _ _ (grp_prop G) _ _ H1)
                              _ _ (@pequiv_to _ _ (grp_prop G) _ _ H2)).
  - intros u v Huv; apply (@pequiv_from _ _ (grp_prop G)).
    rewrite (grp_map_inv (free_grp_extend h) u).
    rewrite (grp_map_inv (free_grp_extend h) v).
    exact (grp_inv_respects_law G _ _ (@pequiv_to _ _ (grp_prop G) _ _ Huv)).
Qed.

Definition fg_ker_idx : FGCongIdx X := existT _ fg_ker fg_ker_is_cong.

(* The mediator out of the quotient.  [Build_GrpHom'] asks only for the
   multiplication law; respectfulness IS [pequiv_to], again as a tactic
   proof, since the source's `≈` is [fg_ker] only after delta. *)
Definition fg_ker_med : QGrp fg_ker fg_ker_is_cong ~{Grp}~> G.
Proof.
  unshelve refine (@Build_GrpHom' (QGrp fg_ker fg_ker_is_cong) G
                     {| morphism := fg_ev |} _).
  - intros u v Huv; exact (@pequiv_to _ _ (grp_prop G) _ _ Huv).
  - intros u v; exact (grp_map_mul (free_grp_extend h) u v).
Defined.

End FreeGrpKernel.

Arguments fg_ev {X G} h w.
Arguments fg_ker {X G} h.
Arguments fg_ker_is_cong {X G} h.
Arguments fg_ker_idx {X G} h.
Arguments fg_ker_med {X G} h.

(** ** The solution set, and the application *)

(* NAMED so that both record fields elaborate [QGrp] at ONE universe
   instance; written inline they mint two. *)
Definition QGrpOf {X : Sets} (i : FGCongIdx X) : obj[Grp] :=
  QGrp (`1 i) (`2 i).

Definition QGrpInsertOf {X : Sets} (i : FGCongIdx X)
  : X ~{Sets}~> Grp_Forget (QGrpOf i) := QGrp_insert (`1 i) (`2 i).

(* THE NON-CIRCULAR SOLUTION SET.  The covering of an [h : X ~> U c] is its
   own kernel congruence, and the covering equation is
   [free_grp_extend_generators] on the nose. *)
Definition Grp_Forget_solution_set_prop (X : Sets) : SolutionSet Grp_Forget X.
Proof.
  unshelve refine (@Build_SolutionSet Grp Sets Grp_Forget X
                     (FGCongIdx X) QGrpOf QGrpInsertOf _).
  intros c h.
  exists (fg_ker_idx h), (fg_ker_med h).
  intro a; simpl.
  exact (free_grp_extend_generators X c h a).
Defined.

(* THE CIRCULAR DISCHARGE, KEPT FOR COMPARISON; A REMOVAL CANDIDATE FOR
   JOHN.  It is named so that the circularity is visible at every use site
   rather than buried in a term: the family is the singleton at the unit of
   the adjunction the theorem is being asked to produce.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): it is no
   longer what [free_group_via_GAFT] consumes.  It is kept because
   Test/ProbeGrpFreeAFT442.v's section A is a block of statements ABOUT it,
   because the naming convention it establishes is what makes the
   circularity legible, and because removing working code is John's
   call. *)
Definition Grp_Forget_solution_set_from_adjunction (X : Sets) :
  SolutionSet Grp_Forget X :=
  solution_set_of_adjunction free_group_adjunction X.

(* UNCONDITIONAL and non-circular since this PR.  The statement is
   unchanged; only the fourth argument moved. *)
Definition free_group_via_GAFT : ∃ F : Sets ⟶ Grp, F ⊣ Grp_Forget :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous)
       Grp_Forget_solution_set_prop.

(* The circular reading of the same application, kept under a name that
   says so.  Its type is the type [free_group_via_GAFT] always had, which
   is why nothing downstream had to change. *)
Definition free_group_via_GAFT_from_adjunction :
  ∃ F : Sets ⟶ Grp, F ⊣ Grp_Forget :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous)
       Grp_Forget_solution_set_from_adjunction.

(* MEASURED, side by side, [About] under [Set Printing Universes] with the
   stdlib bounds ([flip], [Projections], [Morphisms], [eq_rect], …) elided;
   the criterion is every constraint naming only this file's own binders.

     Grp_Forget_solution_set_prop@{u u0 u1 u2 u3 u4} :
       ∀ X : obj[Sets@{u2 u3}], SolutionSet@{u u3 u4 u2} Grp_Forget@{u4 u3 u2} X
     (* Set < u / Set < u4 / u2 < u3 / u2 < u4 / u0 <= u1 / u2 <= u /
        u2 <= u1 *)

     Grp_Forget_solution_set_from_adjunction@{u u0 u1 u2 u3 u4 u5 u6 u7} :
       ∀ X : obj[Sets@{u3 u2}], SolutionSet@{u u2 u0 u3} Grp_Forget@{u0 u2 u3} X
     (* Set < u0 / u3 < u0 / u3 < u2 / u0 <= u5 / u2 <= u6 / u3 <= u7 /
        u4 <= u5 / u4 <= u6 / u4 <= u7 *)

   SIX universes against NINE.  [SolutionSet@{i dobj cobj h}] (GAFT.v),
   so the new family's index slot is [u] and the ambient carrier is [u2]:
   the ONLY two bounds on the index are [Set < u] and [u2 <= u], so
   [u := u2] is expressible and the index sits AT the carrier universe.
   A sigma over the objects of [Grp] would give [carrier < index] instead,
   and that single inequality is the whole wall.

     free_group_via_GAFT@{u u0 u1 u2 u3} :
       ∃ F : Sets@{u0 u} ⟶ Grp@{u u0}, F ⊣ Grp_Forget@{u u u0}
     (* Set < u0 / u0 < u / u0 <= u3 / u2 <= u3 *)

     free_group_via_GAFT_from_adjunction@{u u0 u1 u2 u3 u4 u5 u6 u7 u8} :
       ∃ F : Sets@{u1 u0} ⟶ Grp@{u u1}, F ⊣ Grp_Forget@{u u0 u1}
     (* Set < u / u1 < u / u1 < u0 / u <= u3 / u <= u6 / u0 <= u3 /
        u0 <= u7 / u1 <= u8 / u5 <= u6 / u5 <= u7 / u5 <= u8 *)

   FIVE universes against TEN.  (An earlier draft of this PR's notes said
   NINE for the circular application; measured in this tree it is ten.)

   AND THE ONE SIDE CONDITION IS VISIBLE HERE, but only if the slots are
   read off the right constants, so they are measured rather than guessed:
   [About Sets] gives [Sets@{o so} : Category@{so o o}], so the FIRST
   argument is the setoid CARRIER universe and the second the universe the
   objects live in; [About Grp] gives [Grp@{u p} : Category@{u p p}] with
   the constraints [Set < u] and [p < u] built IN.

   So the circular form's [Set < u] is [Grp]'s own intrinsic bound on its
   OBJECT universe and costs nothing.  The unconditional form's [Set < u0]
   is not: [u0] there is [Sets]'s carrier slot and [Grp]'s hom slot, and no
   constant in the chain forces it.  That is [Set < carrier], the same cost
   Instance/Mod/TensorAFT.v records at [RMod R], and it is the price of
   putting the index AT the carrier universe.

     free_group_monad_via_GAFT@{u u0 u1 u2 u3} : five universes, the
     application's own block verbatim. *)

(* The issue's QA clause: the theorem's output is the functor the tree
   already has.  Left adjoints to a fixed functor are isomorphic, so this
   is [left_adjoint_iso] (Theory/Adjunction.v) and not a computation
   — the two terms are very different, and only `≈` is claimed.

   RESTATED, not rewritten, by this PR.  The body is byte-identical: it
   names [free_group_via_GAFT], and that constant now denotes the
   non-circular application, so this clause is now a comparison between the
   word model and a GAFT output that does not presuppose it.  What the
   restatement is worth: before, both sides of the `≈` came from
   [free_group_adjunction], and the isomorphism was close to a tautology;
   now only the right-hand side does. *)
Definition free_group_via_GAFT_agrees : `1 free_group_via_GAFT ≈ FreeGrp :=
  left_adjoint_iso Grp_Forget _ FreeGrp (`2 free_group_via_GAFT)
                   free_group_adjunction.

(** ** Riehl §5.1: the induced monad on Sets *)

Definition free_group_monad : @Monad Sets (Grp_Forget ◯ FreeGrp) :=
  Adjunction_Induced_Monad free_group_adjunction.

(* Riehl's clause asks for the unit and multiplication to be RECORDED, and
   both are available at [eq_refl] because [Adjunction_Induced_Monad] is a
   [Build_Monad] applied to them (Monad/Comparison.v): the unit is
   the free-group unit and the multiplication is [U] applied to the counit
   at [F X], i.e. "evaluate a word of words". *)

Example free_group_monad_ret (X : Sets) :
  @ret Sets (Grp_Forget ◯ FreeGrp) free_group_monad X = free_group_unit X
  := eq_refl.

Example free_group_monad_join (X : Sets) :
  @join Sets (Grp_Forget ◯ FreeGrp) free_group_monad X
    = fmap[Grp_Forget] (free_group_counit (FreeGrp X))
  := eq_refl.

(* ...and Riehl's description of the underlying endofunctor — a set goes to
   the words in its letters and their formal inverses — is the carrier of
   [(U ◯ F) X], on the nose. *)
Example free_group_monad_carrier (X : Sets) :
  carrier ((Grp_Forget ◯ FreeGrp) X) = FGWord X := eq_refl.

(* THE MONAD ON THE GAFT-PRODUCED ADJUNCTION, added by the PR "algebraic
   carriers are sets" (2026-09-17).

   This is an ADDITION and not a restatement of [free_group_monad], and the
   reason is worth recording rather than hiding behind a name.  The three
   [eq_refl] readbacks above are what Riehl's clause asks for, and they hold
   only because [Adjunction_Induced_Monad] is a [Build_Monad] applied to
   terms that reduce.  [GAFT] is [Qed]-opaque, so NOTHING in its output
   reduces: this monad's unit and multiplication have no [eq_refl]
   readbacks, its carrier does not reduce to [FGWord], and Riehl's clause
   could not be discharged from it.  That is exactly why
   [free_group_monad] is built from the explicit adjunction and is kept.
   What this constant adds is the fact that the monad exists on the
   non-circular adjunction too, which is a statement about the theorem's
   output and not about the word model. *)
Definition free_group_monad_via_GAFT :
  @Monad Sets (Grp_Forget ◯ `1 free_group_via_GAFT) :=
  Adjunction_Induced_Monad (`2 free_group_via_GAFT).

(** ** Awodey §7.2: the underlying-set functor is representable

    [U : Grp ⟶ Sets] is represented by the free group on one generator:
    a homomorphism out of it is exactly an element of the target, which
    is the free/forgetful adjunction read at the singleton.  Nothing in
    the tree represented [Grp_Forget] before this file — the three mentions
    of [Representable] under Instance/Grp/ that predate it are all
    disclaimers. *)

Notation SetOne := unit_setoid_object.

Notation grp_adj G :=
  (@adj Grp Sets FreeGrp Grp_Forget free_group_adjunction SetOne G).

(* The two directions are lifted out of the record literal: inside
   [{| to := … |}] the names [to] and [from] resolve to the fields being
   defined, not to [Isomorphism]'s projections. *)

Program Definition grp_repr_const (G : Grp) (a : carrier (Grp_Forget G)) :
  SetOne ~{Sets}~> Grp_Forget G := {| morphism := fun _ => a |}.

Definition grp_repr_to (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  carrier (Grp_Forget G) := to (grp_adj G) f ttt.

Definition grp_repr_from (G : Grp) (a : carrier (Grp_Forget G)) :
  FreeGrp SetOne ~{Grp}~> G := from (grp_adj G) (grp_repr_const G a).

(* The two naturality facts, proved once here rather than inside the
   instance's obligations.  Each needs a transport step: the transpose's
   naturality is stated against [fmap[U] f ∘ k], and the constant map at
   [f a] is pointwise equal to that but is a different record. *)

Lemma grp_repr_to_natural {x y : Grp} (f : x ~{Grp}~> y)
  (h : FreeGrp SetOne ~{Grp}~> x) :
  grp_repr_to y (f ∘ h) ≈ f (grp_repr_to x h).
Proof.
  exact (@to_adj_nat_r Grp Sets FreeGrp Grp_Forget free_group_adjunction
                       SetOne x y f h ttt).
Qed.

Lemma grp_repr_from_natural {x y : Grp} (f : x ~{Grp}~> y)
  (a : carrier (Grp_Forget x)) (w : carrier (Grp_Forget (FreeGrp SetOne))) :
  grp_repr_from y (f a) w ≈ f (grp_repr_from x a w).
Proof.
  unfold grp_repr_from.
  transitivity (from (grp_adj y) (fmap[Grp_Forget] f ∘ grp_repr_const x a) w).
  - exact (proper_morphism (from (grp_adj y))
             (grp_repr_const y (f a))
             (fmap[Grp_Forget] f ∘ grp_repr_const x a)
             (fun _ => reflexivity _) w).
  - exact (@from_adj_nat_r Grp Sets FreeGrp Grp_Forget free_group_adjunction
                           SetOne x y f (grp_repr_const x a) w).
Qed.

Program Definition Grp_Forget_Representable : Representable Grp_Forget := {|
  repr_obj := FreeGrp SetOne;
  represented :=
    {| to   := {| transform := fun G => {| morphism := grp_repr_to G |} |}
     ; from := {| transform := fun G => {| morphism := grp_repr_from G |} |} |}
|}.
Next Obligation. symmetry; exact (grp_repr_to_natural f x0). Qed.
Next Obligation. exact (grp_repr_to_natural f x0). Qed.
Next Obligation.
  exact (proper_morphism (from (grp_adj G))
           (grp_repr_const G x) (grp_repr_const G y) (fun _ => H) a).
Qed.
Next Obligation. symmetry; exact (grp_repr_from_natural f x0 a). Qed.
Next Obligation. exact (grp_repr_from_natural f x0 a). Qed.
(* The two isomorphism laws are the adjunction's own, read at [ttt].  In
   [Sets] an equation between morphisms is pointwise, so each is the
   corresponding [iso_?_from] applied to a point. *)
Next Obligation. exact (iso_to_from (grp_adj x) (grp_repr_const x x0) ttt). Qed.
Next Obligation.
  unfold grp_repr_from, grp_repr_to.
  transitivity (from (grp_adj x) (to (grp_adj x) x0) a).
  - refine (proper_morphism (from (grp_adj x))
              (grp_repr_const x (to (grp_adj x) x0 ttt))
              (to (grp_adj x) x0) _ a).
    intro u; destruct u; reflexivity.
  - exact (iso_from_to (grp_adj x) x0 a).
Qed.

(** ** Mac Lane §V.6's injectivity clause, and where its argument stops

    The issue's Verification block asks for [Free_Grp_unit_injective]: the
    universal arrow [X → U (F X)] is injective, "by the two-element-group
    separation argument".  Both halves of that are delivered below, and the
    argument's constructive limit is disclosed rather than papered over.

    The general form is one transpose.  If [X] embeds in the underlying set
    of ANY group at all, the unit is injective, because the transpose of the
    embedding factors it through the unit.  That is
    [free_group_unit_injective_of_embedding], and it needs no hypothesis on
    [X] and no reference to the word model.

    Mac Lane's separation argument is the instance that manufactures such an
    embedding out of nothing — for [a] apart from [b], map [X] to Z/2 by the
    characteristic function of [a].  The Z/2 used is Instance/Grp.v's
    [Z2], with its non-triviality; nothing new is built for it, and
    Construction/Deloop.v's [Bool_Xor_Grp] is a DIFFERENT thing — it
    inhabits that file's own record also named [GrpObject], the collision
    that makes Instance/Grp/Free.v import Instance/Grp.v last.  On SETOIDS
    the characteristic function does not exist without a decision procedure
    for [≈], so
    [free_group_unit_injective_dec] carries one, and the uniform statement
    is NOT proved here.  It is also not refuted: the obstruction is to this
    ARGUMENT, not to the conclusion.  Proving it uniformly would mean
    analysing [FreeGroupoidRel] (Construction/Free/Groupoid.v), the
    generated congruence on words, and that file states in terms that it
    offers no normal form and no decision procedure, so every
    negative statement there is proved by mapping into a concrete groupoid
    — which is exactly the route taken here.

    CONFIRMED AND SHARPENED by the PR "algebraic carriers are sets"
    (2026-09-17).  That PR had to give the free group a [Prop]-valued
    equality, and measured that the free groupoid's hom-equality — Construction/
    Quotient.v's [CongClosure] — has no [Prop] mirror out of which the
    [Type]-valued equation can be recovered: a truncation of it cannot be
    eliminated into [Type], and a hand [Prop] mirror inductive has no
    [_rect].  The only shape that would have worked is a normal form, i.e.
    exactly the decision procedure this paragraph says does not exist.  So
    the free group's `≈` is the propositional TRUNCATION of the groupoid's
    (Instance/Grp/Free.v's [fg_equiv]), and the totality of everything below
    over ALL of [Sets] is unaffected: no constant in this file gained a
    hypothesis. *)

Notation grp_adj_at X H :=
  (@adj Grp Sets FreeGrp Grp_Forget free_group_adjunction X H).

(* The transpose of [g] agrees with [g] at the unit.  This is
   [to_adj_unit] composed with [iso_to_from], read pointwise. *)
Lemma free_group_transpose_at_unit {X : Sets} (H : Grp)
      (g : X ~{Sets}~> Grp_Forget H) (a : carrier X) :
  g a ≈ fmap[Grp_Forget] (from (grp_adj_at X H) g) (free_group_unit X a).
Proof.
  transitivity (to (grp_adj_at X H) (from (grp_adj_at X H) g) a).
  - symmetry; exact (iso_to_from (grp_adj_at X H) g a).
  - exact (@to_adj_unit Grp Sets FreeGrp Grp_Forget free_group_adjunction
             X H (from (grp_adj_at X H) g) a).
Qed.

(** Any embedding of [X] into a group's underlying set forces the unit to
    be injective. *)
Theorem free_group_unit_injective_of_embedding {X : Sets} (H : Grp)
        (g : X ~{Sets}~> Grp_Forget H)
        (Hg : ∀ a b : carrier X, g a ≈ g b → a ≈ b)
        (a b : carrier X) :
  free_group_unit X a ≈ free_group_unit X b → a ≈ b.
Proof.
  intro Heq.
  apply Hg.
  transitivity (fmap[Grp_Forget] (from (grp_adj_at X H) g)
                  (free_group_unit X a)).
  { exact (free_group_transpose_at_unit H g a). }
  transitivity (fmap[Grp_Forget] (from (grp_adj_at X H) g)
                  (free_group_unit X b)).
  { exact (proper_morphism (fmap[Grp_Forget] (from (grp_adj_at X H) g))
             (free_group_unit X a) (free_group_unit X b) Heq). }
  symmetry; exact (free_group_transpose_at_unit H g b).
Qed.

(* A decision procedure for a [Sets] object's own [≈].  Stated as a
   [Type]-valued sum rather than [sumbool]: [≈] is a [crelation], so it does
   not fit in [Prop]. *)
Definition SetoidDecidable (X : Sets) : Type :=
  ∀ a b : carrier X, (a ≈ b) + ((a ≈ b) → False).

(* The characteristic map of [a], the separating map of Mac Lane's
   argument.  This is the step that needs [dec]: without it there is no
   function at all, respectfulness aside. *)
Program Definition grp_chi {X : Sets} (dec : SetoidDecidable X)
        (a : carrier X) : X ~{Sets}~> Grp_Forget Z2 := {|
  morphism := fun x => if dec x a then true else false
|}.
Next Obligation.
  proper.
  (* Name the premise by its shape: since #450 made [Z2]'s setoid
     universe-polymorphic the goal reads [Proper (equiv ==> eq)] and
     [proper] no longer calls the premise [H]. *)
  match goal with Hxy : @equiv _ _ _ _ |- _ => rename Hxy into H end.
  destruct (dec x a) as [e1|n1], (dec y a) as [e2|n2]; auto.
  - now destruct (n2 (transitivity (symmetry H) e1)).
  - now destruct (n1 (transitivity H e2)).
Qed.

(** Mac Lane's separation argument, with the decision procedure it needs
    made explicit.  Distinct generators stay distinct in the free group. *)
Theorem free_group_unit_injective_dec {X : Sets} (dec : SetoidDecidable X)
        (a b : carrier X) :
  free_group_unit X a ≈ free_group_unit X b → a ≈ b.
Proof.
  intro Heq.
  destruct (dec a b) as [Hab|Hab]; [exact Hab|].
  (* The two sides disagree at [grp_chi dec a], which the transpose
     forbids. *)
  assert (Hchi : grp_chi dec a a ≈ grp_chi dec a b).
  { transitivity (fmap[Grp_Forget]
                    (from (grp_adj_at X Z2) (grp_chi dec a))
                    (free_group_unit X a)).
    { exact (free_group_transpose_at_unit Z2 (grp_chi dec a) a). }
    transitivity (fmap[Grp_Forget]
                    (from (grp_adj_at X Z2) (grp_chi dec a))
                    (free_group_unit X b)).
    { exact (proper_morphism
               (fmap[Grp_Forget] (from (grp_adj_at X Z2) (grp_chi dec a)))
               (free_group_unit X a) (free_group_unit X b) Heq). }
    symmetry; exact (free_group_transpose_at_unit Z2 (grp_chi dec a) b). }
  simpl in Hchi.
  destruct (dec a a) as [_|Haa]; [| now destruct (Haa (reflexivity a))].
  destruct (dec b a) as [Hba|_]; [| discriminate Hchi].
  now destruct (Hab (symmetry Hba)).
Qed.

(* Non-vacuity, and the connection to what was already in tree.
   Instance/Grp/Free.v's [free_group_two_generators_distinct] is the
   two-letter case, proved by mapping into S3; it is recovered here as an
   instance of the general statement, over Z/2 instead.  The two are
   independent proofs of the same fact, and neither is deleted: the S3 one
   also carries non-commutativity, which Z/2 cannot. *)

Definition TwoLetters_dec : SetoidDecidable TwoLetters :=
  fun a b => match Bool.bool_dec a b with
             | left e  => inl e
             | right n => inr n
             end.

Corollary free_group_two_letters_distinct :
  free_group_unit TwoLetters true ≈ free_group_unit TwoLetters false → False.
Proof.
  intro Heq.
  exact (Bool.diff_true_false
           (free_group_unit_injective_dec TwoLetters_dec true false Heq)).
Qed.
