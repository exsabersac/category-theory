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

(*
   本节说明 SpanningArrow 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition spanning_arrow {x : X} {a : A} (f : x ~> G a) : Type :=
  Spanning f.

(*
   本节说明伴随、拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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


(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
