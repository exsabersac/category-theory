Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/weighted+limit

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * The covariant hom-diagram and its reindexing. *)

Section Weighted.

#[local] Obligation Tactic := idtac.

(*
   本节说明自然变换、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition HomDiagram {J C : Category} (c : C) (F : J ⟶ C) : J ⟶ Sets := {|
  fobj := fun j => {| carrier := c ~{C}~> F j ; is_setoid := @homset C c (F j) |};
  fmap := fun j j' (g : j ~{J}~> j') =>
    {| morphism := fun h => fmap[F] g ∘ h |}
|}.
Next Obligation.
  intros J C c F j j' g h h' Heq; now rewrite Heq.
Qed.
Next Obligation.
  intros J C c F j j' g g' Heq h; simpl; now rewrite Heq.
Qed.
Next Obligation.
  intros J C c F j h; simpl; now rewrite fmap_id, id_left.
Qed.
Next Obligation.
  intros J C c F j j' j'' g g' h; simpl; now rewrite fmap_comp, <- comp_assoc.
Qed.

(*
   本节说明自然变换、（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition HomDiagram_precompose {J C : Category} {c c' : C}
  (h : c' ~{C}~> c) (F : J ⟶ C) : HomDiagram c F ⟹ HomDiagram c' F := {|
  transform := fun j => {| morphism := fun k => k ∘ h |}
|}.
Next Obligation.
  intros J C c c' h F j k k' Heq; now rewrite Heq.
Qed.
Next Obligation.
  intros J C c c' h F j j' g k; simpl; now rewrite comp_assoc.
Qed.
Next Obligation.
  intros J C c c' h F j j' g k; simpl; now rewrite comp_assoc.
Qed.

End Weighted.

(*
   nLab: https://ncatlab.org/nlab/show/weighted+limit

   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class WeightedLimit {J C : Category} (W : J ⟶ Sets) (F : J ⟶ C) := {
  wlim_obj : C;

  wlim_iso (c : C) :
    @Isomorphism Sets
      ([[[J,Sets]]](W, HomDiagram c F))
      {| carrier := c ~{C}~> wlim_obj ; is_setoid := @homset C c wlim_obj |};

  (*
   本节说明 Weighted 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  wlim_natural (c c' : C) (h : c' ~{C}~> c)
    (α : W ⟹ HomDiagram c F) :
    to (wlim_iso c') (nat_compose (HomDiagram_precompose h F) α)
      ≈ to (wlim_iso c) α ∘ h
}.

Arguments wlim_obj {J C W F} _.
Arguments wlim_iso {J C W F} _ _.
Arguments wlim_natural {J C W F} _ _ _ _ _.

(*
   本节说明自然变换、（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Conical.

#[local] Obligation Tactic := idtac.

Context {J : Category}.
Context {C : Category}.
Context {F : J ⟶ C}.

(* A Sets-natural transformation out of the constant-singleton weight is a cone:
   read off the leg at [j] by evaluating the [j]-component at the unique point. *)

Program Definition cone_of_nat (c : C)
  (α : Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram c F) : ACone c F := {|
  vertex_map := fun j => α j ttt
|}.
Next Obligation.
  intros c α x y f.
  exact (@naturality _ _ _ _ α x y f ttt).
Qed.

(* Conversely a cone yields a Sets-natural transformation out of the
   constant-singleton weight: each component is the constant map at that leg. *)

Program Definition nat_of_cone (c : C) (κ : ACone c F) :
  Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram c F := {|
  transform := fun j => {| morphism := fun _ => @vertex_map _ _ _ _ κ j |}
|}.
Next Obligation.
  repeat intro; reflexivity.
Qed.
Next Obligation.
  intros c κ x y f u; simpl.
  now rewrite (@cone_coherence _ _ _ _ κ x y f).
Qed.
Next Obligation.
  intros c κ x y f u; simpl.
  symmetry; now rewrite (@cone_coherence _ _ _ _ κ x y f).
Qed.

End Conical.

(* * WeightedLimit ⇒ Limit at the constant weight. *)

Lemma limit_of_conical `(F : J ⟶ C) :
  WeightedLimit (Δ[J]( @terminal_obj Sets Sets_Terminal )) F → Limit F.
Proof.
  intro WL.
  destruct WL as [L Φ Φnat].
  (* The universal cone at apex [L]: the legs classified by [id[L]]. *)
  pose (β := from (Φ L) id[L]).
  unshelve refine {| limit_cone :=
    {| vertex_obj := L ; coneFrom := cone_of_nat (F:=F) L β |} |}.
  intro N.
  pose (n := @vertex_obj _ _ _ N).
  pose (αN := nat_of_cone (F:=F) n (@coneFrom _ _ _ N)).
  unshelve refine {| unique_obj := to (Φ n) αN |}.
  - (* The classified map mediates: φ x ∘ (to (Φ n) αN) ≈ ψ x. *)
    intro x.
    pose (u := to (Φ n) αN).
    (* Classifying the [u]-reindexed universal cone reproduces [u]. *)
    assert (Hu : to (Φ n) (nat_compose (HomDiagram_precompose u F) β) ≈ u).
    { transitivity (to (Φ L) β ∘ u).
      - exact (Φnat L n u β).
      - assert (Htb : to (Φ L) β ≈ id[L]).
        { exact (iso_to_from (Φ L) id[L]). }
        rewrite Htb; apply id_left. }
    (* Hence the reindexed cone equals [αN], read off leg by leg. *)
    assert (Hpre : nat_compose (HomDiagram_precompose u F) β ≈ αN).
    { transitivity
        (from (Φ n) (to (Φ n) (nat_compose (HomDiagram_precompose u F) β))).
      - symmetry.
        exact (iso_from_to (Φ n) (nat_compose (HomDiagram_precompose u F) β)).
      - transitivity (from (Φ n) (to (Φ n) αN)).
        + apply (proper_morphism (from (Φ n))); exact Hu.
        + exact (iso_from_to (Φ n) αN). }
    exact (Hpre x ttt).
  - (* Uniqueness of the mediator. *)
    intros v Hv.
    assert (Hv2 : to (Φ n) (nat_compose (HomDiagram_precompose v F) β) ≈ v).
    { transitivity (to (Φ L) β ∘ v).
      - exact (Φnat L n v β).
      - assert (Htb : to (Φ L) β ≈ id[L]).
        { exact (iso_to_from (Φ L) id[L]). }
        rewrite Htb; apply id_left. }
    assert (Hpre : nat_compose (HomDiagram_precompose v F) β ≈ αN).
    { intros j w; destruct w; exact (Hv j). }
    transitivity (to (Φ n) (nat_compose (HomDiagram_precompose v F) β)).
    + apply (proper_morphism (to (Φ n))); symmetry; exact Hpre.
    + exact Hv2.
Defined.

(* * Limit ⇒ WeightedLimit at the constant weight. *)

Section Reverse.

#[local] Obligation Tactic := idtac.

Context {J : Category}.
Context {C : Category}.
Context {F : J ⟶ C}.
Context (Lim : Limit F).

Definition Lobj : C := @vertex_obj _ _ _ (@limit_cone _ _ _ Lim).

Definition Lleg (x : J) : Lobj ~{C}~> F x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ Lim)) x.

Lemma Lleg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ Lleg x ≈ Lleg y.
Proof.
  exact (@cone_coherence _ _ _ _
           (@coneFrom _ _ _ (@limit_cone _ _ _ Lim)) x y f).
Qed.

Definition mkCone {c : C} (κ : ACone c F) : Cone F :=
  {| vertex_obj := c ; coneFrom := κ |}.

Definition Lmed (N : Cone F) : @vertex_obj _ _ _ N ~{C}~> Lobj :=
  unique_obj (@ump_limits _ _ _ Lim N).

Lemma Lmed_commutes (N : Cone F) (x : J) :
  Lleg x ∘ Lmed N ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.
Proof. exact (unique_property (@ump_limits _ _ _ Lim N) x). Qed.

Lemma Lmed_unique (N : Cone F) (v : @vertex_obj _ _ _ N ~{C}~> Lobj) :
  (∀ x : J, Lleg x ∘ v ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x) →
  Lmed N ≈ v.
Proof. intro H. exact (uniqueness (@ump_limits _ _ _ Lim N) v H). Qed.

(* The classifying map: a cone from [c] is sent to its mediating morphism. *)

Definition wl_to_fn (c : C)
  (α : Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram c F) :
  c ~{C}~> Lobj :=
  Lmed (mkCone (cone_of_nat c α)).

Program Definition wl_to (c : C) :
  SetoidMorphism
    ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram c F))
    {| carrier := c ~{C}~> Lobj ; is_setoid := @homset C c Lobj |} :=
  {| morphism := wl_to_fn c |}.
Next Obligation.
  intros c α α' Heq; unfold wl_to_fn.
  apply (Lmed_unique (mkCone (cone_of_nat c α))); intro x.
  transitivity (@vertex_map _ _ _ _ (cone_of_nat c α') x).
  - exact (Lmed_commutes (mkCone (cone_of_nat c α')) x).
  - symmetry; exact (Heq x ttt).
Qed.

(* Its inverse: a map [u : c ~> Lobj] is sent to the cone obtained by
   postcomposing every limit leg with [u]. *)

Program Definition wl_from_acone (c : C) (u : c ~{C}~> Lobj) : ACone c F := {|
  vertex_map := fun j => Lleg j ∘ u
|}.
Next Obligation.
  intros c u x y f; simpl.
  rewrite comp_assoc; now rewrite Lleg_coherence.
Qed.

Definition wl_from_fn (c : C) (u : c ~{C}~> Lobj) :
  Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram c F :=
  nat_of_cone c (wl_from_acone c u).

Program Definition wl_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C}~> Lobj ; is_setoid := @homset C c Lobj |}
    ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram c F)) :=
  {| morphism := wl_from_fn c |}.
Next Obligation.
  intros c u u' Heq j w; simpl.
  now rewrite Heq.
Qed.

Program Definition wl_iso (c : C) :
  @Isomorphism Sets
    ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram c F))
    {| carrier := c ~{C}~> Lobj ; is_setoid := @homset C c Lobj |} :=
  {| to := wl_to c ; from := wl_from c |}.
Next Obligation.
  (* to ∘ from ≈ id : classifying the [u]-cone recovers [u]. *)
  intros c u; unfold wl_to_fn, wl_from_fn.
  apply (Lmed_unique (mkCone (cone_of_nat c (nat_of_cone c (wl_from_acone c u)))));
    intro x; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* from ∘ to ≈ id : the classified map carries [α]'s legs. *)
  intros c α j w; destruct w; unfold wl_from_fn, wl_to_fn; simpl.
  exact (Lmed_commutes (mkCone (cone_of_nat c α)) j).
Qed.

Program Definition conical_of_limit_inst :
  WeightedLimit (Δ[J]( @terminal_obj Sets Sets_Terminal )) F := {|
  wlim_obj := Lobj;
  wlim_iso := wl_iso
|}.
Next Obligation.
  (* Naturality: both sides mediate the [h]-reindexed cone. *)
  intros c c' h α.
  apply (Lmed_unique
           (mkCone (cone_of_nat c' (nat_compose (HomDiagram_precompose h F) α))));
    intro x.
  transitivity ((Lleg x ∘ Lmed (mkCone (cone_of_nat c α))) ∘ h).
  - rewrite comp_assoc; reflexivity.
  - rewrite (Lmed_commutes (mkCone (cone_of_nat c α)) x); reflexivity.
Qed.

End Reverse.

Lemma conical_of_limit `(F : J ⟶ C) :
  Limit F → WeightedLimit (Δ[J]( @terminal_obj Sets Sets_Terminal )) F.
Proof. intro Lim. exact (conical_of_limit_inst Lim). Qed.

(*
   nLab: https://ncatlab.org/nlab/show/weighted+limit

   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem conical_weighted `(F : J ⟶ C) :
  WeightedLimit (Δ[J]( @terminal_obj Sets Sets_Terminal )) F ↔ Limit F.
Proof.
  split.
  - apply limit_of_conical.
  - apply conical_of_limit.
Defined.

(*
   nLab: https://ncatlab.org/nlab/show/weighted+colimit

   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition WeightedColimit {J C : Category} (W : (J^op) ⟶ Sets) (F : J ⟶ C) :=
  @WeightedLimit (J^op) (C^op) W (F^op).
