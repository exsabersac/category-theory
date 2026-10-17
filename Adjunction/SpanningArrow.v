Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.

Generalizable All Variables.

(*
   nLab:  https://ncatlab.org/nlab/show/subobject
   nLab:  https://ncatlab.org/nlab/show/solution+set+condition

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SpanningArrow.

Context {A X : Category}.
Context (G : A ⟶ X).

(* f : x ~> G a FACTORS THROUGH the subobject m of a when it lifts along
   G (sub_mono m).  The lift is data, as everywhere in this library. *)
Definition SubFactorsThrough {x : X} {a : A} (f : x ~> G a) (m : SubObj a) :
  Type :=
  { k : x ~> G (sub_dom m) & fmap[G] (sub_mono m) ∘ k ≈ f }.

(* Mac Lane's definition, stated POSITIVELY as a cancellation law: f
   spans a when every subobject of a through which f factors is already
   the whole of a, i.e. lies above the top subobject [sub_top] (so its
   mono is an isomorphism).  "Proper subobject" -- one for which
   [sub_le sub_top m] does not hold -- never needs to be named, exactly
   as Adjunction/SAFT.v's [Cogenerator] avoids "distinct arrows". *)
Definition Spanning {x : X} {a : A} (f : x ~> G a) : Type :=
  ∀ m : SubObj a, SubFactorsThrough f m → sub_le sub_top m.

(* The issue's pinned name, an alias of [Spanning] -- the same Type, so
   that the verification block's [Print Assumptions spanning_arrow] has a
   referent.  Every statement below is about [Spanning]. *)
Definition spanning_arrow {x : X} {a : A} (f : x ~> G a) : Type :=
  Spanning f.

(* G preserves wide pullbacks OF MONOS -- intersections of subobjects,
   exactly what Mac Lane's Lemma asks G to preserve: the image under G
   of a wide pullback cone over a family of monos is again a wide
   pullback cone.  A first draft quantified over arbitrary families, a
   hypothesis strictly stronger than Mac Lane's; an audit flagged it and
   the monicity clause [Hm] was added at integration.  Since #453 it has
   a necessity lemma: Adjunction/SAFT/Characterization.v's
   [right_adjoint_PreservesWidePullbacks] proves it for every right
   adjoint, and [SAFT_iff] there uses it as the second clause of Mac
   Lane's §V.8 Theorem 2. *)
Definition PreservesWidePullbacks : Type :=
  ∀ (I : Type) (B : I → A) (z : A) (g : ∀ i, B i ~> z)
    (Hm : ∀ i, Monic (g i)) (P : A) (p : ∀ i, P ~> B i),
    IsWidePullback g P p →
    IsWidePullback (fun i => fmap[G] (g i)) (G P) (fun i => fmap[G] (p i)).

(* The index of the solution set the lemma delivers: the spanning arrows
   out of x, with their codomains. *)
Definition SpanningArrowsOutOf (x : X) : Type :=
  { a : A & { f : x ~> G a & Spanning f } }.

End SpanningArrow.

Arguments SubFactorsThrough {A X} G {x a} f m.
Arguments Spanning {A X} G {x a} f.
Arguments spanning_arrow {A X} G {x a} f.
Arguments PreservesWidePullbacks {A X} G.
Arguments SpanningArrowsOutOf {A X} G x.

(** ** Elementary closure properties, before any hypothesis on A or G *)

Section SpanningElementary.

Context {A X : Category}.
Context (G : A ⟶ X).

Lemma factors_through_top {x : X} {a : A} (f : x ~> G a) :
  SubFactorsThrough G f (sub_top (x:=a)).
Proof.
  exists f; simpl.
  rewrite fmap_id; cat.
Defined.

Lemma spanning_respects {x : X} {a : A} (f f' : x ~> G a) :
  f ≈ f' → Spanning G f → Spanning G f'.
Proof.
  intros Hf Hs m [k Hk].
  apply Hs.
  exists k.
  now rewrite Hk.
Defined.

Lemma spanning_precompose_split_epi {x x' : X} {a : A}
  (f : x ~> G a) (e : x' ~> x) (s : x ~> x') (Hes : e ∘ s ≈ id) :
  Spanning G f → Spanning G (f ∘ e).
Proof.
  intros Hs m [k Hk].
  apply Hs.
  exists (k ∘ s).
  rewrite comp_assoc, Hk, <- comp_assoc, Hes; cat.
Defined.

Corollary spanning_precompose_iso {x x' : X} {a : A}
  (f : x ~> G a) (i : x' ≅ x) : Spanning G f → Spanning G (f ∘ to i).
Proof.
  exact (spanning_precompose_split_epi f (to i) (from i) (iso_to_from i)).
Defined.

Lemma spanning_of_top_only {x : X} {a : A} (f : x ~> G a)
  (H : ∀ m : SubObj a, sub_le sub_top m) : Spanning G f.
Proof. intros m _; exact (H m). Defined.


(* The two facts below were first proved in Instance/Variety/Spanning.v,
   the parallel witness half of #448, under a "CANDIDATE FOR this file"
   note, and were lifted here at integration; the variety file consumes
   [spanning_forces_top], while [sub_le_top_iso] is stated for the
   reading it gives and is not yet consumed anywhere.  Neither re-proves
   a lattice fact: they TRANSPORT
   Theory/Subobject/Lattice.v's [sub_top_greatest] and its
   [sub_le_antisym]. *)

(* A subobject that the top subobject factors through has an invertible
   mono: the factor is its inverse, the other triangle by monicity.  This
   is the sense in which Mac Lane's "factors through no proper subobject"
   is recovered from the positive form of [Spanning]. *)
Lemma sub_le_top_iso {a : A} (m : SubObj a) (H : sub_le sub_top m) :
  IsIsomorphism (sub_mono m).
Proof.
  destruct H as [k Hk]; simpl in Hk.
  unshelve econstructor.
  - exact k.
  - exact Hk.
  - apply (monic (Monic:=sub_is_monic m)).
    rewrite comp_assoc, Hk.
    now rewrite id_left, id_right.
Defined.

(* Mac Lane's own words, read back: a spanning arrow factors through no
   subobject other than the top one, at ≈ on [SubObj]. *)
Lemma spanning_forces_top {x : X} {a : A} (f : x ~> G a) (Hf : Spanning G f)
  (m : SubObj a) (Hm : SubFactorsThrough G f m) : m ≈ sub_top.
Proof.
  apply sub_le_antisym.
  - exact (sub_top_greatest m).
  - exact (Hf m Hm).
Defined.

End SpanningElementary.

Arguments sub_le_top_iso {_ _} _ _.
Arguments spanning_forces_top {_ _} _ {_ _} _ _ _ _.

(** ** Mac Lane's Lemma 2: factoring through a spanning arrow *)

Section SpanningLemma.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

Section AtAnArrow.

Context {x : X} {a : A}.
Context (f : x ~> G a).

Definition FactoringFamily : Type :=
  { m : SubObj a & SubFactorsThrough G f m }.

Definition factoring_sub (j : FactoringFamily) : SubObj a := `1 j.

Definition factoring_lift (j : FactoringFamily) :
  x ~> G (sub_dom (factoring_sub j)) := `1 (`2 j).

Lemma factoring_lift_commutes (j : FactoringFamily) :
  fmap[G] (sub_mono (factoring_sub j)) ∘ factoring_lift j ≈ f.
Proof. exact (`2 (`2 j)). Qed.

Definition factoring_top : FactoringFamily :=
  (sub_top; factors_through_top G f).

Definition factoring_wpull :
  WidePullback (fun j => sub_mono (factoring_sub j)) :=
  wide_pullback (fun j => sub_mono (factoring_sub j)).

Definition spanning_sub : SubObj a :=
  sub_wide_intersection factoring_sub factoring_top factoring_wpull.

Definition spanning_sub_IsIntersection :
  IsIntersection factoring_sub spanning_sub :=
  sub_wide_intersection_IsIntersection factoring_sub factoring_top
    factoring_wpull.

Definition spanning_wpull_preserved :
  IsWidePullback (fun j => fmap[G] (sub_mono (factoring_sub j)))
                 (G (WPull factoring_wpull))
                 (fun j => fmap[G] (wide_pullback_proj factoring_wpull j)) :=
  GP FactoringFamily (fun j => sub_dom (factoring_sub j)) a
     (fun j => sub_mono (factoring_sub j))
     (fun j => sub_is_monic (factoring_sub j))
     (WPull factoring_wpull) (wide_pullback_proj factoring_wpull)
     (wide_pullback_is_pullback factoring_wpull).

Lemma factoring_lifts_agree (i j : FactoringFamily) :
  fmap[G] (sub_mono (factoring_sub i)) ∘ factoring_lift i
    ≈ fmap[G] (sub_mono (factoring_sub j)) ∘ factoring_lift j.
Proof. now rewrite !factoring_lift_commutes. Qed.

Definition spanning_mediator :
  ∃! u : x ~> G (WPull factoring_wpull),
    ∀ j : FactoringFamily,
      fmap[G] (wide_pullback_proj factoring_wpull j) ∘ u ≈ factoring_lift j :=
  wpull_ump spanning_wpull_preserved factoring_lift factoring_lifts_agree.

Definition spanning_factor : x ~> G (sub_dom spanning_sub) :=
  unique_obj spanning_mediator.

Lemma spanning_factor_lifts (j : FactoringFamily) :
  fmap[G] (wide_pullback_proj factoring_wpull j) ∘ spanning_factor
    ≈ factoring_lift j.
Proof. exact (unique_property spanning_mediator j). Qed.

Theorem spanning_factor_commutes :
  fmap[G] (sub_mono spanning_sub) ∘ spanning_factor ≈ f.
Proof.
  change (sub_mono spanning_sub)
    with (sub_mono (factoring_sub factoring_top)
            ∘ wide_pullback_proj factoring_wpull factoring_top).
  rewrite fmap_comp, <- comp_assoc.
  rewrite spanning_factor_lifts.
  apply factoring_lift_commutes.
Qed.

Lemma spanning_sub_least (m : SubObj a) :
  SubFactorsThrough G f m → sub_le spanning_sub m.
Proof.
  intro Hm.
  exact (inter_le factoring_sub spanning_sub spanning_sub_IsIntersection
           (m; Hm)).
Defined.

Theorem spanning_factor_spanning : Spanning G spanning_factor.
Proof.
  intros n [l Hl].
  assert (Hm' : SubFactorsThrough G f (sub_compose spanning_sub n)).
  { exists l.
    change (sub_mono (sub_compose spanning_sub n))
      with (sub_mono spanning_sub ∘ sub_mono n).
    rewrite fmap_comp, <- comp_assoc, Hl.
    exact spanning_factor_commutes. }
  destruct (spanning_sub_least (sub_compose spanning_sub n) Hm') as [k Hk].
  exists k; simpl.
  apply (monic (Monic := sub_is_monic spanning_sub)).
  rewrite id_right, comp_assoc.
  exact Hk.
Defined.

End AtAnArrow.

Definition factors_through_spanning {x : X} {a : A} (f : x ~> G a) :
  { m : SubObj a & { f' : x ~> G (sub_dom m)
                   & Spanning G f' * (fmap[G] (sub_mono m) ∘ f' ≈ f) } } :=
  (spanning_sub f;
     (spanning_factor f;
        (spanning_factor_spanning f, spanning_factor_commutes f))).

(** ** The solution set the lemma delivers *)

Definition spanning_solution_set (x : X) : SolutionSet G x.
Proof using A G GP HWP X.
  unshelve refine
    {| sol_index := SpanningArrowsOutOf G x
     ; sol_obj := fun i => `1 i
     ; sol_arr := fun i => `1 (`2 i) |}.
  intros c h.
  destruct (factors_through_spanning h) as [m [f' [Hsp Hcom]]].
  exact ((sub_dom m; (f'; Hsp)); (sub_mono m; Hcom)).
Defined.

End SpanningLemma.

(** ** Mac Lane's use of the lemma: GAFT without a separate solution set *)

(* WHY THIS SECTION EXISTS -- AND A RECORDED CORRECTION: ITS REASON NO
   LONGER HOLDS, THOUGH THE SECTION IS STILL WHAT THE FILE SHIPS.

   An earlier revision of this comment read, in full:

     "MEASURED UNIVERSE PIN, and the reason this section exists.  With
      Set Printing Universes, [About GAFT] reports
        GAFT@{u u0 u1 u2 u3 u4} :
          ∀ {C : Category@{u1 Set Set}} {D : Category@{u2 Set Set}} ...
      -- Adjunction/GAFT.v is pinned at hom = proof = Set in BOTH
      arguments.  The pin is ATTRIBUTED BY About, not guessed: of the
      five constants GAFT's proof consumes, [Comma_Complete],
      [wif_of_sols], [Complete_HasEqualizers] and [GAFT_from_initials]
      all report a free hom universe, and [initial_from_weakly_initial]
      (Theory/WeaklyInitial.v) reports
        initial_from_weakly_initial@{u u0 u1 u2} :
          ∀ {C : Category@{u2 Set Set}} ...
      so that is the carrier.  (Instance/One.v's [_1],
      Instance/Parallel.v's [Parallel] and Instance/Discrete.v's
      [DiscreteCat] are each free in h, measured the same way; an earlier
      draft of this comment named them and was wrong.)  Nothing above
      carries the pin: [spanning_solution_set] is polymorphic in the hom
      universe, as the header's About records.  Feeding it to [GAFT]
      inside Section SpanningLemma is therefore REFUSED, with
        universe inconsistency: Cannot enforce Set = <the hom universe of A>
      so the corollary is stated here instead, over categories annotated
      at Set."

   Every step of that attribution was correct, and it located the pin one
   link further back than [initial_from_weakly_initial]: at
   Instance/Discrete.v's then-unannotated [DiscreteCat_Functor], which
   [initial_from_weakly_initial] takes two limits over.  That donor was
   annotated in place at Instance/Discrete.v in the PR "algebraic
   carriers are sets" (2026-09-17).  Measured after it:

     GAFT@{cobj dobj h u u0 u1} :
       ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} ...

   -- no [Set], both hom universes free -- and the refusal quoted above
   NO LONGER OCCURS.  Re-measured directly: the very [exact] below,
   restated in a section whose A and X are declared at free hom
   universes, is ACCEPTED, reporting
   [GAFT_from_spanning_free@{oA hA oX hX …}] with [Complete@{hA hA hA oA}]
   and no [Set] anywhere.

   The section below is nonetheless left AS IT STANDS, annotated at [Set],
   because that PR changed prose only; widening it is a change to the
   statement of a shipped theorem and belongs to its own commit.  What the
   [Set] annotation now is, therefore, is a RESTRICTION THIS FILE IMPOSES
   and no longer one it inherits -- and it was never a claim that spanning
   arrows need small hom-sets.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): the own
   commit anticipated in the paragraph above is this one, and the widening
   has been made.  The [Universes oA oX.] line and the two [@{oA Set Set}]
   / [@{oX Set Set}] annotations are GONE; [A] and [X] are now declared
   bare, and the elaborator arrives at free object and hom levels for both.
   Nothing else in the section changed -- the statement, the [Proof using]
   list and the one-line [exact] are untouched -- so no theorem was lost
   and none was weakened.  Measured, [About] under [Set Printing
   Universes]:

     BEFORE (8 universes)
       GAFT_from_spanning@{oA oX u u0 u1 u2 u3 u4} :
         ∀ {A : Category@{oA Set Set}} {X : Category@{oX Set Set}}
           (G : A ⟶ X),
         HasWidePullbacks@{u u oA Set} A →
         PreservesWidePullbacks@{oA Set oX Set u0 u1 u1 u1} G →
         Complete@{Set Set Set oA} →
         PreservesImageLimit@{oA Set oX Set u3 Set u4 Set} → ∃ F : X ⟶ A, F ⊣ G
       (* … Set = oA / u = u1 *)

     AFTER (13 universes)
       GAFT_from_spanning@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11} :
         ∀ {A : Category@{u u0 u0}} {X : Category@{u1 u2 u2}} (G : A ⟶ X),
         HasWidePullbacks@{u3 u4 u u0} A →
         PreservesWidePullbacks@{u u0 u1 u2 u5 u6 u7 u8} G →
         Complete@{u0 u0 u0 u} →
         PreservesImageLimit@{u u0 u1 u0 u10 u0 u11 u0} → ∃ F : X ⟶ A, F ⊣ G
       (* … u <= u0 / u0 <= u2 / u2 < u10 / u2 < u11 / u3 < u5 / u6 < u5 … *)

   No [Set] anywhere, and in particular the BEFORE block's [Set = oA] --
   which demanded a category whose OBJECTS as well as homs live in [Set] --
   is gone.  [spanning_solution_set] never carried the pin and its
   [About] is unchanged.

   WHAT THE WIDENING DOES NOT BUY.  It does not make the theorem reach
   [RMod R].  The AFTER block reads [u <= u0], objects at or below homs,
   and [RMod R] has homs strictly below objects; feeding it is still
   refused, now with "Cannot enforce u_hom = b because u_hom < u_obj <= b"
   rather than with the old [Set] message.  That refusal, and the
   independent fact that [HasWidePullbacks (RMod R)] is itself universe-
   refused, are recorded at Instance/Mod/Spanning.v and pinned as
   NEGATIVE 2 of Test/ProbeModTensorAFT449.v.  The route that DOES reach
   [RMod R] is the congruence-indexed solution set of
   Instance/Mod/TensorAFT.v, which goes through [representability_theorem]
   and not through this section. *)

Section GAFTFromSpanning.

Context {A : Category}.
Context {X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

Theorem GAFT_from_spanning (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) : { F : X ⟶ A & F ⊣ G }.
Proof using A G GP HWP X.
  exact (GAFT G comp cont (spanning_solution_set G GP)).
Qed.

End GAFTFromSpanning.
