Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.

Generalizable All Variables.

(*
   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Definition3.

Context {C : Category}.
Context (K : C ⟶ Sets).

(** ** Mac Lane §V.6 Definition 3: the solution set condition, element-wise

    A set of objects and ELEMENTS through which every element factors.  This
    is Definition 3 as the book states it; [SolutionSet] of Adjunction/GAFT.v
    is the hom-shaped form, and the two agree at the singleton set. *)

(* The INDEX universe is named [i], and it is free of it: the constraint
   block relates it to nothing, exactly as in [SolutionSet].  It is the
   LAST binder, because the three the enclosing section discharges (the
   ambient's object and hom-and-proof levels, and [Sets]' object level)
   come first and print with generic names.  Measured readback:

     ElementSolutionSet@{u u0 u1 i} :
     ∀ {C : Category@{u u0 u0}}, (C ⟶ Sets@{u0 u1}) → Type@{max(u,u0,i+1)}
     (* u u0 u1 i |= u0 < u1 / u0 <= ID.u0 *)

   [representability_theorem] below is where [i] is pinned, to the ambient
   hom universe, exactly as in [GAFT]: see its own binders. *)
Record ElementSolutionSet@{i} := {
  esol_index : Type@{i};
  esol_obj : esol_index → C;
  esol_elem : ∀ i, K (esol_obj i);
  esol_covers {c : C} (x : K c) :
    { i : esol_index & { t : esol_obj i ~{C}~> c
                       & fmap[K] t (esol_elem i) ≈ x } }
}.

(** ** The two forms agree at the singleton

    Elements of [K c] are global points [1 ~> K c] — Theory/Universal/
    Element.v's [global_element] and [global_elements_iso], which already
    exist; nothing here re-proves that bridge. *)

(* Both passages carry the index TYPE across on the nose — the four
   [eq_refl] readbacks below say so.  At the level of the index UNIVERSE
   the two directions differ, and the difference is measured rather than
   assumed:

     sols_of_esols@{u u0 u1 i u2 u3 u4} :
       … ElementSolutionSet@{u u0 u1 i} K
         → SolutionSet@{i u1 u u0} K SetsOne
     (* u u0 u1 i u2 u3 u4 |= u0 < u1 / u3 <= ID.u0 *)

   -- [i] on the nose in this direction, the index universe reappearing
   verbatim in [SolutionSet]'s first slot; and

     esols_of_sols@{u u0 u1 i u2 u3 u4 u5} :
       … SolutionSet@{u5 u1 u u0} K SetsOne
         → ElementSolutionSet@{u u0 u1 i} K
     (* u u0 u1 i u2 u3 u4 u5 |= u0 < u1 / u5 <= i *)

   -- a BOUND, [u5 <= i], in the other, since the record is built rather
   than projected.  Stated because "the same index" is true of the types
   and only up to [<=] of the levels. *)
Definition sols_of_esols@{i +} (E : ElementSolutionSet@{i})
  : SolutionSet K SetsOne.
Proof.
  unshelve refine
    {| sol_index := esol_index E
     ; sol_obj := esol_obj E
     ; sol_arr := fun i => global_element (esol_elem E i) |}.
  intros c h.
  destruct (esol_covers E (h ttt)) as [i [t e]].
  exists i, t.
  intro u; destruct u; exact e.
Defined.

Definition esols_of_sols@{i +} (S : SolutionSet K SetsOne)
  : ElementSolutionSet@{i}.
Proof.
  unshelve refine
    {| esol_index := sol_index S
     ; esol_obj := sol_obj S
     ; esol_elem := fun i => sol_arr S i ttt |}.
  intros c x.
  destruct (sol_covers S (global_element x)) as [i [t e]].
  exists i, t.
  exact (e ttt).
Defined.

(* Both passages keep the index and the objects on the nose. *)
Example sols_of_esols_index (E : ElementSolutionSet) :
  sol_index (sols_of_esols E) = esol_index E := eq_refl.

Example sols_of_esols_obj (E : ElementSolutionSet) (i : esol_index E) :
  sol_obj (sols_of_esols E) i = esol_obj E i := eq_refl.

Example esols_of_sols_index (S : SolutionSet K SetsOne) :
  esol_index (esols_of_sols S) = sol_index S := eq_refl.

Example esols_of_sols_elem (S : SolutionSet K SetsOne) (i : sol_index S) :
  esol_elem (esols_of_sols S) i = sol_arr S i ttt := eq_refl.

(** ** A representation out of an initial object of the elements comma *)

Definition representable_of_comma_initial (I : @Initial (=(SetsOne) ↓ K)) :
  Representable K :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement
       (AUniversalElement_of_AUniversalArrow K _
          (aua_of_ua (Build_UniversalArrow SetsOne K I)))).

End Definition3.

Arguments ElementSolutionSet {C} K.
Arguments esol_index {C K} _.
Arguments esol_obj {C K} _ _.
Arguments esol_elem {C K} _ _.

(** ** Mac Lane §V.6 Theorem 3

    Stated at top level, and the binders carry the SAME size condition as
    [GAFT], which is where it comes from ([comma_initial_of_sols]):

      (i)  [ElementSolutionSet@{cobj h su h} K] -- the element-solution-set
           INDEX universe (the last slot) is the ambient hom universe [h].
           The record leaves it free; this theorem pins it.
      (ii) [@Complete@{h h h cobj} C] -- [Complete]'s shape-object universe
           is [h] too, for the reason Adjunction/GAFT.v spells out: the
           equalizer of all endomorphisms of the product is a limit over a
           shape whose objects are a hom-set.

    RECORDED CORRECTION.  An earlier revision of this comment read
    "[comma_initial_of_sols] pins the hom AND proof universes of both
    categories to [Set] (GAFT's own pin), and inside a section that has
    already elaborated [Sets] the ascription is refused."  That [Set] was
    a universe-minimization artifact of Instance/Discrete.v's unannotated
    [DiscreteCat_Functor] and is gone (PR "algebraic carriers are sets",
    2026-09-17); the theorem is still stated at top level, and (i)+(ii)
    are why.  The refusals that Instance/Mod/TensorAFT.v records against
    this theorem survive the repair, re-measured there: they are (i)
    meeting an index one universe above the ring's carrier, with no [Set]
    in the message.

    Measured readback:

      representability_theorem@{cobj h su u u0 u1 u2 u3 u4 u5 u6 u7 u8} :
      ∀ {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su}),
        Complete@{h h h cobj}
        → PreservesImageLimit@{cobj h su h u h su h}
          → ElementSolutionSet@{cobj h su h} K
            → Representable@{u u0 su cobj h} K
      (* cobj h su … |= h < su / u6 <= u4 *) *)

Definition representability_theorem@{cobj h su +}
  {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet@{cobj h su h} K) : Representable K :=
  representable_of_comma_initial K
    (comma_initial_of_sols K SetsOne comp cont (sols_of_esols K E)).

(** ** Transport of a representation along a natural isomorphism *)

Definition Representable_transport {C : Category} {F G : C ⟶ Sets}
  (i : F ≅[[C, Sets]] G) (R : Representable F) : Representable G :=
  {| repr_obj := @repr_obj C F R
   ; represented := iso_compose i (@represented C F R) |}.

Example Representable_transport_obj {C : Category} {F G : C ⟶ Sets}
  (i : F ≅[[C, Sets]] G) (R : Representable F) :
  @repr_obj C G (Representable_transport i R) = @repr_obj C F R := eq_refl.

(** ** §V.8 Exercise 1, forward: a left adjoint makes the functor representable

    [HomAfter K 1] IS [Hom(1,−) ◯ K] on the nose, and global points make it
    [K] itself, so #348's [adj_representable] at the singleton transports
    onto [K]. *)

Section Ex81.

Context {C : Category}.
Context (K : C ⟶ Sets).

Example homafter_one_is_composite :
  HomAfter K SetsOne = Compose (fobj[Curried_Hom Sets] SetsOne) K := eq_refl.

#[local] Obligation Tactic :=
  simpl; intros;
  repeat match goal with [ H : poly_unit |- _ ] => destruct H end;
  try (srewrite (@fmap_id _ _ K); reflexivity); try reflexivity.

Program Definition homafter_one_iso : HomAfter K SetsOne ≅[[C, Sets]] K := {|
  to   := {| transform := fun c => global_elements_to (K c) |};
  from := {| transform := fun c => global_elements_from (K c) |}
|}.

Definition representable_of_left_adjoint {L : Sets ⟶ C} (A : L ⊣ K) :
  Representable K :=
  Representable_transport homafter_one_iso (adj_representable A SetsOne).

(* The representing object is the left adjoint at the singleton. *)
Example representable_of_left_adjoint_obj {L : Sets ⟶ C} (A : L ⊣ K) :
  @repr_obj C K (representable_of_left_adjoint A) = L SetsOne := eq_refl.

End Ex81.

(** ** The converse leg: a representable functor is continuous *)

Definition continuous_of_representable {C : Category} {K : C ⟶ Sets}
  (R : Representable K) : ContinuousFunctor K :=
  representable_iso_ContinuousFunctor (@repr_obj C K R)
    (iso_equiv (@represented C K R)).

Definition preserves_image_of_representable {C : Category} {K : C ⟶ Sets}
  (R : Representable K) : @PreservesImageLimit C Sets K :=
  Continuous_PreservesImageLimit (continuous_of_representable R).

(** ** Theorem 3 as a biconditional

    A representation supplies its own element-wise solution set: the single
    object is the representing one and the single element is the identity
    read across the isomorphism. *)

Theorem representability_iff {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) :
  (@PreservesImageLimit C Sets K * ElementSolutionSet K)%type
    ↔ Representable K.
Proof.
  split.
  - intros [cont E]; exact (representability_theorem K comp cont E).
  - intro R.
    split.
    + exact (preserves_image_of_representable R).
    + unshelve refine {| esol_index := poly_unit
                       ; esol_obj := fun _ => @repr_obj C K R
                       ; esol_elem := fun _ =>
                           transform[to (@represented C K R)]
                             (@repr_obj C K R) id |}.
      intros c x.
      exists ttt.
      exists (transform[from (@represented C K R)] c x).
      pose proof (@naturality _ _ _ _ (to (@represented C K R))
                    (@repr_obj C K R) c
                    (transform[from (@represented C K R)] c x) id) as N.
      simpl in N.
      rewrite id_right in N.
      rewrite N.
      pose proof (iso_to_from (@represented C K R) c x) as HH;
        simpl in HH; rewrite HH; srewrite (@fmap_id _ _ K c); reflexivity.
Defined.

Example representability_iff_fst {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet K) :
  fst (representability_iff K comp) (cont, E)
    = representability_theorem K comp cont E := eq_refl.

(** ** Riehl 4.7.14: SAFT's hypotheses give representability *)

(* CORRECTION, #453: "SAFT's hypotheses" here are Adjunction/SAFT.v's,
   whose covering datum [cover] is refutable (the header).  The passage
   over the book's hypotheses is Adjunction/SAFT/Characterization/
   Corollaries.v's [continuous_Set_functor_representable]; this
   constant is kept as it was. *)

Definition saft_representable {C : Category} (K : C ⟶ Sets)
  (comp : @Complete C) (cont : @PreservesImageLimit C Sets K)
  (G : Cogenerator C) (WP : ∀ x : C, SubobjectIndex x)
  (cover : SubobjectCover K comp G WP) : Representable K :=
  representable_of_left_adjoint K (projT2 (SAFT K comp cont G WP cover)).

(** ** §V.8 Exercise 1, converse: copowers give the left adjoint

    The tree's copowers (Structure/Limit/Power.v from #321, with #366's
    Structure/Limit/Power/Adjunction.v) are indexed by a
    bare [Type] and so yield plain functions out of the index, where a
    [Sets]-valued adjunction needs setoid morphisms respecting [≈]; a
    setoid-indexed copower is not in the tree.  [HasSetsCopowers] is that
    missing structure, stated exactly as the representability #348's
    biconditional consumes it — so the converse lands as an axiom-free
    CONDITIONAL, and the condition is, by that same biconditional, "the
    represented functor has a left adjoint". *)

Definition HasSetsCopowers (C : Category) : Type :=
  ∀ (b : C) (X : Sets),
    Representable (HomAfter (fobj[@Curried_Hom C] b) X).

Section Ex81Converse.

Context {C : Category}.
Context {K : C ⟶ Sets}.
Context (R : Representable K).

#[local] Notation r := (@repr_obj C K R).

(* Whiskering [K ≅ [Hom r,−)] by [Hom_Sets(X,−)]. *)
#[local] Obligation Tactic := idtac.

Program Definition homafter_whisker (X : Sets) :
  HomAfter K X ≅[[C, Sets]] HomAfter (fobj[@Curried_Hom C] r) X := {|
  to   := {| transform := fun c =>
    {| morphism := fun f => transform[from (@represented C K R)] c ∘ f |} |};
  from := {| transform := fun c =>
    {| morphism := fun f => transform[to (@represented C K R)] c ∘ f |} |}
|}.
Next Obligation. intros X c u v Huv z; simpl; now rewrite (Huv z). Qed.
Next Obligation.
  intros X x y f u z; simpl.
  exact (@naturality _ _ _ _ (from (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X x y f u z; simpl.
  symmetry.
  exact (@naturality _ _ _ _ (from (@represented C K R)) x y f (u z)).
Qed.
Next Obligation. intros X c u v Huv z; simpl; now rewrite (Huv z). Qed.
Next Obligation.
  intros X x y f u z; simpl.
  exact (@naturality _ _ _ _ (to (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X x y f u z; simpl.
  symmetry.
  exact (@naturality _ _ _ _ (to (@represented C K R)) x y f (u z)).
Qed.
Next Obligation.
  intros X c u z; simpl.
  pose proof (iso_from_to (@represented C K R) c (u z)) as HH;
    simpl in HH; rewrite HH; now rewrite id_left.
Qed.
Next Obligation.
  intros X c u z; simpl.
  pose proof (iso_to_from (@represented C K R) c (u z)) as HH;
    simpl in HH; rewrite HH; srewrite (@fmap_id _ _ K c); reflexivity.
Qed.

Definition left_adjoint_of_representable_Sets (cop : HasSetsCopowers C) :
  { L : Sets ⟶ C & L ⊣ K } :=
  fst (adjunction_iff_pointwise_representable K)
      (fun X => Representable_transport
                  (iso_sym (homafter_whisker X)) (cop r X)).

End Ex81Converse.

(** ** Witnesses at Sets

    Two functors, each with every premise discharged in tree. *)

(** *** The points functor [Hom(1,−)] on Sets *)

Definition Sets_points : Sets ⟶ Sets := @HomFrom Sets SetsOne.

Definition Sets_points_esol : ElementSolutionSet Sets_points.
Proof.
  unshelve refine
    {| esol_index := poly_unit
     ; esol_obj := fun _ => SetsOne
     ; esol_elem := fun _ =>
         (@id Sets SetsOne : carrier (fobj[Sets_points] SetsOne)) |}.
  intros c x.
  exists ttt, x.
  simpl; intro u; destruct u; simpl.
  reflexivity.
Defined.

(* The single member is the singleton itself, and the single element is its
   identity — which is what keeps [Sets_points_esol] transparent. *)
Example Sets_points_esol_obj (u : esol_index Sets_points_esol) :
  esol_obj Sets_points_esol u = SetsOne := eq_refl.

Definition Sets_points_cont : @PreservesImageLimit Sets Sets Sets_points :=
  Continuous_PreservesImageLimit (hom_ContinuousFunctor SetsOne).

Definition Sets_points_repr : Representable Sets_points :=
  representability_theorem Sets_points Sets_Complete Sets_points_cont
    Sets_points_esol.

(* The object the theorem produces represents the same functor as the
   singleton does, so the two agree up to the canonical isomorphism. *)
Definition Sets_points_iso :
  @repr_obj Sets Sets_points Sets_points_repr ≅ SetsOne :=
  repr_unique_iso (Hom_Representable SetsOne) Sets_points_repr.

(** *** The identity functor on Sets, both routes *)

Definition Sets_Id_esol : ElementSolutionSet (@Id Sets) :=
  esols_of_sols (@Id Sets) (Sets_Id_SolutionSet SetsOne).

Definition Sets_Id_repr : Representable (@Id Sets) :=
  representability_theorem (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_esol.

Definition Sets_Id_repr_iso :
  @repr_obj Sets (@Id Sets) Sets_Id_repr ≅ SetsOne :=
  repr_unique_iso (Representable_transport global_elements_natural
                     (Hom_Representable SetsOne)) Sets_Id_repr.

(* And by Exercise V.8.1's forward direction, from GAFT's own adjunction. *)
Definition Sets_Id_repr_of_adjoint : Representable (@Id Sets) :=
  representable_of_left_adjoint (@Id Sets) (projT2 GAFT_at_Sets_Id).

Example Sets_Id_repr_of_adjoint_obj :
  @repr_obj Sets (@Id Sets) Sets_Id_repr_of_adjoint
    = projT1 GAFT_at_Sets_Id SetsOne := eq_refl.
