Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(** * The copower is left adjoint to the power *)

(*
   nLab:      https://ncatlab.org/nlab/show/power
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** The power as an endofunctor of [C]

    The arrow action is the mediator [power_desc] produces for the family
    [j ↦ g ∘ ev j], and every functor law is one appeal to that mediator's
    uniqueness clause followed by a computation with [power_fmap_ev]. *)

Section PowerFunctor.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context (J : Type).

Definition power_fmap {b b' : C} (g : b ~> b') : power J b ~> power J b' :=
  unique_obj (power_desc (power_ump J b')
                (fun j : J => g ∘ power_ev J b j)).

(* The characterizing equation of the arrow action: it commutes with the
   evaluations.  This is the mediator's [unique_property], nothing more. *)
Lemma power_fmap_ev {b b' : C} (g : b ~> b') (j : J) :
  power_ev J b' j ∘ power_fmap g ≈ g ∘ power_ev J b j.
Proof. exact (unique_property (power_desc (power_ump J b') _) j). Qed.

Program Definition Power_Functor : C ⟶ C := {|
  fobj := fun b => power J b;
  fmap := fun b b' g => power_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply (uniqueness (power_desc (power_ump J b') _)).
  intros j; rewrite power_fmap_ev; now rewrite Hg.
Qed.
Next Obligation.
  intros b.
  apply (uniqueness (power_desc (power_ump J b) _)).
  intros j; rewrite id_left; apply id_right.
Qed.
Next Obligation.
  intros x y z f g.
  apply (uniqueness (power_desc (power_ump J z) _)).
  intros j.
  rewrite comp_assoc, power_fmap_ev.
  rewrite <- !comp_assoc; now rewrite power_fmap_ev.
Qed.

Example power_functor_obj (b : C) :
  fobj[Power_Functor] b = power J b := eq_refl.

Example power_functor_fmap {b b' : C} (g : b ~> b') :
  fmap[Power_Functor] g = power_fmap g := eq_refl.

(* [power_fmap_ev] restated through [fmap], which is the spelling the
   adjunction's naturality goals present. *)
Lemma power_functor_ev {b b' : C} (g : b ~> b') (j : J) :
  power_ev J b' j ∘ fmap[Power_Functor] g ≈ g ∘ power_ev J b j.
Proof. exact (power_fmap_ev g j). Qed.

End PowerFunctor.

Arguments power_fmap {C HP} J {b b'} g.
Arguments Power_Functor {C HP} J.
Arguments power_functor_ev {C HP} J {b b'} g j.

(** ** The copower as an endofunctor, for free

    [copower J b] is [@power (C^op) HC J b] DEFINITIONALLY (#321), so the
    copower functor is the op-power functor read back through
    [Opposite_Functor].  That is a plain [Definition] with no obligation and
    no tactic; the four [Example]s below record by [eq_refl] exactly what it
    costs, namely nothing. *)

Section CopowerFunctor.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition Copower_Functor : C ⟶ C :=
  Opposite_Functor (@Power_Functor (C^op) HC J).

Example copower_functor_obj (b : C) :
  fobj[Copower_Functor] b = copower J b := eq_refl.

Example copower_functor_fmap {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor] g = @power_fmap (C^op) HC J b' b g := eq_refl.

(* The double opposite returns the op-power functor ON THE NOSE, which is
   what makes [C ⟶ C] the right type rather than [(C^op)^op ⟶ (C^op)^op]. *)
Example copower_functor_double_op :
  Opposite_Functor Copower_Functor = @Power_Functor (C^op) HC J := eq_refl.

(* And the arrow action IS the mediator [copower_desc] produces, read
   covariantly: no [^op] appears in this statement. *)
Example copower_functor_desc {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor] g
  = unique_obj (copower_desc (copower_ump J b)
                  (fun j : J => copower_inj J b' j ∘ g)) := eq_refl.

Lemma copower_functor_inj {b b' : C} (g : b ~> b') (j : J) :
  fmap[Copower_Functor] g ∘ copower_inj J b j
  ≈ copower_inj J b' j ∘ g.
Proof. exact (@power_fmap_ev (C^op) HC J b' b g j). Qed.

End CopowerFunctor.

Arguments Copower_Functor {C HC} J.
Arguments copower_functor_inj {C HC} J {b b'} g j.

(** ** Mac Lane §IV.2 Exercise 12

    The hom-set isomorphism is the composite of #321's two bijections.  The
    two land at the SAME [Sets]-power -- [copower_hom_iso_at] at
    [J ⋔ C(b,c)] read from the copower side, [power_hom_iso_at] at the same
    object read from the power side -- so no comparison map is needed and
    [cp_adj_iso] is supplied by [:=]. *)

Section CopowerPowerAdjunction.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(* The shared right-hand side of the two bijections: the [Sets]-power of the
   hom-setoid [C(b,c)] by [J].  Naming it lets each donor be ASCRIBED at a
   type mentioning it, which is what says they meet ON THE NOSE. *)
Definition cp_middle (b c : C) : Sets :=
  @power Sets Sets_HasIndexedProducts J
    {| carrier := @hom C b c ; is_setoid := @homset C b c |}.

(* Each donor lands at [cp_middle b c] with no comparison map inserted --
   these are the two donors supplied AS TERMS at that ascribed type, so a
   change to either target breaks them.  A tautology [X = X] would say
   nothing here, and is deliberately not what is written. *)
Example cp_copower_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle b c) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

Example cp_power_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C b (power J c)
     ; is_setoid := @homset C b (power J c) |} (cp_middle b c) :=
  power_hom_iso_at (@power_ump C HP J c) b.

Definition cp_adj_iso (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Copower_Functor J] b) c
     ; is_setoid := @homset C (fobj[Copower_Functor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  iso_compose (iso_sym (power_hom_iso_at (@power_ump C HP J c) b))
              (copower_hom_iso_at (@copower_ump C HC J b) c).

(* The forward transpose of [u] is the unique arrow whose [j]-th evaluation
   is [u] precomposed with the [j]-th injection -- Mac Lane's correct
   [C(X · a, c) ≅ Set(X, C(a,c))], read at one pair of objects. *)
Lemma cp_to_char (b c : C) (u : copower J b ~> c) (j : J) :
  power_ev J c j ∘ to (cp_adj_iso b c) u ≈ u ∘ copower_inj J b j.
Proof. exact (unique_property (power_desc (power_ump J c) _) j). Qed.

Lemma cp_to_uniq {b c : C} (u : copower J b ~> c) (v : b ~> power J c) :
  (∀ j : J, power_ev J c j ∘ v ≈ u ∘ copower_inj J b j) →
  to (cp_adj_iso b c) u ≈ v.
Proof.
  intros H.
  exact (uniqueness (power_desc (power_ump J c)
           (fun j : J => u ∘ copower_inj J b j)) v H).
Qed.

(* Mac Lane §IV.2 Ex 12: the copower is left adjoint to the power. *)
Definition Copower_Power_Adjunction : Copower_Functor J ⊣ Power_Functor J.
Proof.
  unshelve eapply (Build_Adjunction' cp_adj_iso).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc, cp_to_char.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    symmetry; exact (copower_functor_inj J g j).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc.
    rewrite (power_functor_ev J f j).
    rewrite <- !comp_assoc; now rewrite (cp_to_char x y g j).
Defined.

(* The adjunction's own hom-set isomorphism IS the composite, and both its
   legs are the mediators of the two universal properties, on the nose. *)
Example cp_adj_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J) Copower_Power_Adjunction b c
  = cp_adj_iso b c := eq_refl.

Example cp_to_readback (b c : C) (u : copower J b ~> c) :
  to (cp_adj_iso b c) u
  = unique_obj (power_desc (power_ump J c)
                  (fun j : J => u ∘ copower_inj J b j)) := eq_refl.

Example cp_from_readback (b c : C) (v : b ~> power J c) :
  from (cp_adj_iso b c) v
  = unique_obj (copower_desc (copower_ump J b)
                  (fun j : J => power_ev J c j ∘ v)) := eq_refl.

End CopowerPowerAdjunction.

Arguments cp_adj_iso {C HP HC} J b c.
Arguments Copower_Power_Adjunction {C HP HC} J.

(** ** C. The weighted-limit presentation, and that it agrees

    Mac Lane's §III.4 power is an indexed product; Structure/Limit/Weighted.v
    presents limits by a WEIGHT.  The power is the weighted limit over the
    TERMINAL SHAPE [1] whose weight picks out the index SET and whose diagram
    is constant at [b].  Both directions are proved: [power_WeightedLimit]
    inhabits the class at the chosen power, and [power_of_weighted] shows
    that ANY weighted limit for that weight and diagram IS a power.  Dually
    for the copower and [WeightedColimit]. *)

Section WeightedPower.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context (J : Type).
Context (b : C).

(* The weight picks out [J] as a DISCRETE setoid.  Discreteness is what the
   backward leg's respectfulness needs: evaluations are indexed by ELEMENTS,
   so a coarser index setoid would demand [ev j ≈ ev j'] from [j ≈ j']. *)
Definition index_setoid : Sets :=
  {| carrier := J ; is_setoid := eq_Setoid J |}.

Definition power_weight : _1 ⟶ Sets := Δ[_1]( index_setoid ).

Definition power_diagram : _1 ⟶ C := Δ[_1]( b ).

Definition wpow_to_fn (c : C)
  (a : power_weight ⟹ HomDiagram c power_diagram) : c ~> power J b :=
  unique_obj (power_desc (power_ump J b) (fun j : J => a ttt j)).

Program Definition wpow_to (c : C) :
  SetoidMorphism ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram))
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |} :=
  {| morphism := wpow_to_fn c |}.
Next Obligation.
  intros c a a' Heq; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b) (fun j : J => a ttt j))).
  intro j.
  transitivity ((fun j0 : J => a' ttt j0) j).
  - exact (unique_property
             (power_desc (power_ump J b) (fun j0 : J => a' ttt j0)) j).
  - simpl; symmetry; exact (Heq ttt j).
Qed.

Program Definition wpow_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |}
    ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram)) :=
  {| morphism := fun u =>
       {| transform := fun _ =>
            {| morphism := fun j => power_ev J b j ∘ u |} |}
   |}.
Next Obligation. intros c u i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c u u' Heq x j; simpl; now rewrite Heq. Qed.

Program Definition wpow_iso (c : C) :
  @Isomorphism Sets ([[[_1,Sets]]](power_weight, HomDiagram c power_diagram))
    {| carrier := c ~{C}~> power J b
     ; is_setoid := @homset C c (power J b) |} :=
  {| to := wpow_to c ; from := wpow_from c |}.
Next Obligation.
  intros c u; simpl; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b)
                       (fun j : J => power_ev J b j ∘ u))).
  intro j; reflexivity.
Qed.
Next Obligation.
  intros c a x j; destruct x; simpl; unfold wpow_to_fn.
  exact (unique_property
           (power_desc (power_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Program Definition power_WeightedLimit :
  WeightedLimit power_weight power_diagram := {|
  wlim_obj := power J b ;
  wlim_iso := wpow_iso
|}.
Next Obligation.
  intros c c' h a; simpl; unfold wpow_to_fn.
  apply (uniqueness (power_desc (power_ump J b)
            (fun j : J => (a ttt j) ∘ h))).
  intro j.
  rewrite comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (unique_property
           (power_desc (power_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Example power_weighted_obj : wlim_obj power_WeightedLimit = power J b
  := eq_refl.

End WeightedPower.

Arguments power_diagram {C} b.

Section WeightedCopower.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

(* The colimit weight is contravariant on the shape, so it lives over
   [1^op].  That shape is NOT [1] -- refuted at [eq_refl] and pinned -- which
   is why this half is built directly rather than instantiated at [C^op]. *)
Definition copower_weight : (Opposite _1) ⟶ Sets :=
  @Diagonal Sets (Opposite _1) (index_setoid J).

Definition copower_diagram : _1 ⟶ C := @Diagonal C _1 b.

Definition wcop_to_fn (c : C)
  (a : copower_weight
         ⟹ HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)) :
  copower J b ~{C}~> c :=
  unique_obj (copower_desc (copower_ump J b) (fun j : J => a ttt j)).

Program Definition wcop_to (c : C) :
  SetoidMorphism
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)))
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |} :=
  {| morphism := wcop_to_fn c |}.
Next Obligation.
  intros c a a' Heq; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b) (fun j : J => a ttt j))).
  intro j.
  transitivity ((fun j0 : J => a' ttt j0) j).
  - exact (unique_property
             (copower_desc (copower_ump J b) (fun j0 : J => a' ttt j0)) j).
  - simpl; symmetry; exact (Heq ttt j).
Qed.

Program Definition wcop_from (c : C) :
  SetoidMorphism
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |}
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram))) :=
  {| morphism := fun u =>
       {| transform := fun _ =>
            {| morphism := fun j => u ∘[C] copower_inj J b j |} |}
   |}.
Next Obligation. intros c u i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c u x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c u u' Heq x j; simpl; now rewrite Heq. Qed.

Program Definition wcop_iso (c : C) :
  @Isomorphism Sets
    ([[[Opposite _1,Sets]]](copower_weight,
       HomDiagram (C:=C^op) c (Opposite_Functor copower_diagram)))
    {| carrier := c ~{C^op}~> copower J b
     ; is_setoid := @homset (C^op) c (copower J b) |} :=
  {| to := wcop_to c ; from := wcop_from c |}.
Next Obligation.
  intros c u; simpl; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b)
                       (fun j : J => u ∘[C] copower_inj J b j))).
  intro j; reflexivity.
Qed.
Next Obligation.
  intros c a x j; destruct x; simpl; unfold wcop_to_fn.
  exact (unique_property
           (copower_desc (copower_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Program Definition copower_WeightedColimit :
  WeightedColimit copower_weight copower_diagram := {|
  wlim_obj := copower J b ;
  wlim_iso := wcop_iso
|}.
Next Obligation.
  intros c c' h a; simpl; unfold wcop_to_fn.
  apply (uniqueness (copower_desc (copower_ump J b)
            (fun j : J => h ∘[C] (a ttt j)))).
  intro j.
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity |].
  exact (unique_property
           (copower_desc (copower_ump J b) (fun j0 : J => a ttt j0)) j).
Qed.

Example copower_weighted_obj :
  wlim_obj copower_WeightedColimit = copower J b := eq_refl.

End WeightedCopower.

Arguments copower_diagram {C} b.

(** ** C'. The converses: a weighted limit for that data IS a power

    This is what turns §C from "the chosen power inhabits the class" into an
    agreement of the two presentations, which is the issue's stated reviewer
    check.  Nothing here assumes the ambient category has powers at all. *)

Section WeightedPowerConverse.

Context {C : Category}.
Context (J : Type).
Context (b : C).
Context (WL : WeightedLimit (power_weight J) (power_diagram b)).

(* A family read as a weighted cone.  Respectfulness is free because
   [index_setoid J] is DISCRETE; naturality is [id_left] twice. *)
Program Definition wpow_cone (c : C) (pi : ∀ _ : J, c ~> b) :
  power_weight J ⟹ HomDiagram c (power_diagram b) := {|
  transform := fun _ => {| morphism := pi |}
|}.
Next Obligation. intros c pi i x y Hxy; simpl in Hxy; subst; reflexivity. Qed.
Next Obligation. intros c pi x y f j; simpl; now rewrite id_left. Qed.
Next Obligation. intros c pi x y f j; simpl; now rewrite id_left. Qed.

(* The generic element: transport the identity back across [wlim_iso]. *)
Definition wpow_ev (j : J) : wlim_obj WL ~> b :=
  from (wlim_iso WL (wlim_obj WL)) id ttt j.

(* The only place [wlim_natural] is spent: the inverse transpose of [u] is
   the generic element precomposed with [u]. *)
Lemma wpow_from_is_precompose (c : C) (u : c ~> wlim_obj WL) (j : J) :
  from (wlim_iso WL c) u ttt j ≈ wpow_ev j ∘ u.
Proof.
  unfold wpow_ev.
  set (al := from (wlim_iso WL (wlim_obj WL)) id).
  set (uc := nat_compose (HomDiagram_precompose u (power_diagram b)) al).
  assert (Hnat : to (wlim_iso WL c) uc ≈ u).
  { unfold uc; rewrite (wlim_natural WL (wlim_obj WL) c u al).
    assert (Ht : to (wlim_iso WL (wlim_obj WL)) al ≈ id).
    { unfold al; exact (iso_to_from (wlim_iso WL (wlim_obj WL)) id). }
    rewrite Ht; apply id_left. }
  assert (Hb : from (wlim_iso WL c) (to (wlim_iso WL c) uc)
                 ≈ from (wlim_iso WL c) u).
  { apply proper_morphism; exact Hnat. }
  transitivity (from (wlim_iso WL c) (to (wlim_iso WL c) uc) ttt j).
  - symmetry; exact (Hb ttt j).
  - exact (iso_from_to (wlim_iso WL c) uc ttt j).
Qed.

Definition power_of_weighted : IsPower b (wlim_obj WL) wpow_ev.
Proof.
  apply Build_IsPower; intros c pi.
  exists (to (wlim_iso WL c) (wpow_cone c pi)).
  - intro j.
    rewrite <- (wpow_from_is_precompose c _ j).
    exact (iso_from_to (wlim_iso WL c) (wpow_cone c pi) ttt j).
  - intros v Hv.
    rewrite <- (iso_to_from (wlim_iso WL c) v).
    apply proper_morphism.
    intros x j; destruct x; simpl.
    rewrite (wpow_from_is_precompose c v j).
    symmetry; exact (Hv j).
Defined.

End WeightedPowerConverse.

Section WeightedCopowerConverse.

Context {C : Category}.
Context (J : Type).
Context (b : C).
Context (WL : WeightedColimit (copower_weight J) (copower_diagram b)).

Program Definition wcop_cocone (c : C) (iota : ∀ _ : J, b ~{C}~> c) :
  copower_weight J
    ⟹ HomDiagram (C:=C^op) c (Opposite_Functor (copower_diagram b)) := {|
  transform := fun _ => {| morphism := iota |}
|}.
Next Obligation.
  intros c iota i x y Hxy; simpl in Hxy; subst; reflexivity.
Qed.
Next Obligation. intros c iota x y f j; simpl; now rewrite id_right. Qed.
Next Obligation. intros c iota x y f j; simpl; now rewrite id_right. Qed.

Definition wcop_inj (j : J) : b ~{C}~> wlim_obj WL :=
  from (wlim_iso WL (wlim_obj WL)) id ttt j.

Lemma wcop_from_is_postcompose (c : C) (u : wlim_obj WL ~{C}~> c)
  (j : J) : from (wlim_iso WL c) u ttt j ≈ u ∘[C] wcop_inj j.
Proof.
  unfold wcop_inj.
  set (al := from (wlim_iso WL (wlim_obj WL)) id).
  set (uc := nat_compose
               (HomDiagram_precompose (C:=C^op) u
                  (Opposite_Functor (copower_diagram b))) al).
  assert (Hnat : to (wlim_iso WL c) uc ≈ u).
  { unfold uc; rewrite (wlim_natural WL (wlim_obj WL) c u al).
    assert (Ht : to (wlim_iso WL (wlim_obj WL)) al ≈ id).
    { unfold al; exact (iso_to_from (wlim_iso WL (wlim_obj WL)) id). }
    rewrite Ht; cat. }
  assert (Hb : from (wlim_iso WL c) (to (wlim_iso WL c) uc)
                 ≈ from (wlim_iso WL c) u).
  { apply proper_morphism; exact Hnat. }
  transitivity (from (wlim_iso WL c) (to (wlim_iso WL c) uc) ttt j).
  - symmetry; exact (Hb ttt j).
  - exact (iso_from_to (wlim_iso WL c) uc ttt j).
Qed.

Definition copower_of_weighted : IsCopower b (wlim_obj WL) wcop_inj.
Proof.
  apply Build_IsCopower; intros c iota.
  exists (to (wlim_iso WL c) (wcop_cocone c iota)).
  - intro j.
    rewrite <- (wcop_from_is_postcompose c _ j).
    exact (iso_from_to (wlim_iso WL c) (wcop_cocone c iota) ttt j).
  - intros v Hv.
    rewrite <- (iso_to_from (wlim_iso WL c) v).
    apply proper_morphism.
    intros x j; destruct x; simpl.
    rewrite (wcop_from_is_postcompose c v j).
    symmetry; exact (Hv j).
Defined.

End WeightedCopowerConverse.

(* The round trip returns the chosen data with ONE identity residue on each
   side, exhibited here rather than described. *)

Section WeightedRoundTrip.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

Definition wrt_ev (j : J) : power J b ~{C}~> b :=
  wpow_ev J b (power_WeightedLimit J b) j.

Example wrt_ev_residue (j : J) : wrt_ev j = power_ev J b j ∘[C] id
  := eq_refl.

Lemma wrt_ev_equiv (j : J) : wrt_ev j ≈ power_ev J b j.
Proof. exact (@id_right C _ _ (power_ev J b j)). Qed.

Definition wrt_inj (j : J) : b ~{C}~> copower J b :=
  wcop_inj J b (copower_WeightedColimit J b) j.

Example wrt_inj_residue (j : J) : wrt_inj j = id ∘[C] copower_inj J b j
  := eq_refl.

Lemma wrt_inj_equiv (j : J) : wrt_inj j ≈ copower_inj J b j.
Proof. exact (@id_left C _ _ (copower_inj J b j)). Qed.

End WeightedRoundTrip.

(** ** D0. The copower BIFUNCTOR, which BOTH parameter readings share

    [(b, J) ↦ J · b] is functorial in both arguments at once.  §D fixes the
    OBJECT and varies the index (Mac Lane's Ex 1 reads the object as the
    parameter); §E fixes the index and varies the object.  They are two
    parametrizations of this ONE bifunctor, and neither implies the other.

    The index category is [Coq], not [Sets], and that is FORCED: the copower
    injections are indexed by ELEMENTS, so [fmap_respects] demands
    [f j = f' j] at LEIBNIZ equality from [f ≈ f'].  [Coq]'s hom-setoid is
    pointwise Leibniz and supplies it; [Sets]' does not, and the probe
    carries an axiom-free countermodel refuting the CANONICAL arrow action
    over [Sets] -- the copower mediator of the injections -- outright rather
    than merely recording that the obvious proof does not go through.  No
    other arrow action over [Sets] is claimed refuted. *)

Section CopowerBifunctor.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.

Definition cop_bifun_fmap (p q : C * Type)
  (gf : (fst p ~{C}~> fst q) * (snd p ~{Coq}~> snd q)) :
  copower (snd p) (fst p) ~> copower (snd q) (fst q) :=
  unique_obj (copower_desc (copower_ump (snd p) (fst p))
    (fun j : snd p =>
       copower_inj (snd q) (fst q) (snd gf j) ∘ fst gf)).

Lemma cop_bifun_inj (p q : C * Type)
  (gf : (fst p ~{C}~> fst q) * (snd p ~{Coq}~> snd q)) (j : snd p) :
  cop_bifun_fmap p q gf ∘ copower_inj (snd p) (fst p) j
    ≈ copower_inj (snd q) (fst q) (snd gf j) ∘ fst gf.
Proof.
  exact (unique_property (copower_desc (copower_ump (snd p) (fst p)) _) j).
Qed.

Program Definition Copower_Bifunctor : C ∏ Coq ⟶ C := {|
  fobj := fun p => copower (snd p) (fst p) ;
  fmap := fun p q gf => cop_bifun_fmap p q gf
|}.
Next Obligation.
  intros p q gf gf' [Hg Hf].
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j; rewrite cop_bifun_inj.
  destruct gf as [g f], gf' as [g' f']; simpl in *.
  rewrite Hg; now rewrite (Hf j).
Qed.
Next Obligation.
  intros p.
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j; simpl; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros p q r gf hk.
  apply (uniqueness (copower_desc (copower_ump (snd p) (fst p)) _)).
  intros j.
  rewrite <- comp_assoc, cop_bifun_inj.
  rewrite comp_assoc, cop_bifun_inj.
  now rewrite <- !comp_assoc.
Qed.

Example copower_bifunctor_obj (J : Type) (b : C) :
  fobj[Copower_Bifunctor] (b, J) = copower J b := eq_refl.

Example copower_bifunctor_partial_obj (J : Type) (b : C) :
  fobj[Partial_l Copower_Bifunctor J] b = fobj[Copower_Functor J] b
  := eq_refl.

Example copower_bifunctor_partial_fmap (J : Type) {b b' : C} (g : b ~> b') :
  fmap[Partial_l Copower_Bifunctor J] g = fmap[Copower_Functor J] g
  := eq_refl.

End CopowerBifunctor.

Arguments Copower_Bifunctor {C HC}.

(** ** D1. Mac Lane §IV.7 Exercise 1, UNRESTRICTED

    The displayed isomorphism of the exercise, in its CORRECTED form
    [C(J · a, c) ≅ Set(J, C(a,c))], upgraded from a family of bijections to
    an isomorphism of BIFUNCTORS on [C^op ∏ C] -- which is what "natural in
    the parameter a" asks for.  No hypothesis beyond [HasIndexedCoproducts].

    The right-hand side is [Power_Functor] AT [Sets] composed with the
    hom-bifunctor: Mac Lane's [Set(J, −)] is §A's own power functor. *)

Section ObjectParameterUnrestricted.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition CopLeft : C^op ∏ C ⟶ Sets :=
  Hom C ◯ ((Opposite_Functor (Copower_Functor J)) ∏⟶ Id[C]).

Definition CopRight : C^op ∏ C ⟶ Sets :=
  @Power_Functor Sets Sets_HasIndexedProducts J ◯ Hom C.

Example copleft_obj (a c : C) :
  fobj[CopLeft] (a, c)
  = {| carrier := @hom C (copower J a) c
     ; is_setoid := @homset C (copower J a) c |} := eq_refl.

Example copright_obj (a c : C) :
  fobj[CopRight] (a, c)
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C a c ; is_setoid := @homset C a c |} := eq_refl.

Program Definition cop_nat : CopLeft ⟹ CopRight := {|
  transform := fun p =>
    to (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p))
|}.
Next Obligation.
  intros [a c] [a' c'] [h k] u j; simpl in *.
  rewrite <- !comp_assoc.
  now rewrite (@power_fmap_ev (C^op) HC J a a' h j).
Qed.
Next Obligation.
  intros [a c] [a' c'] [h k] u j; simpl in *.
  rewrite <- !comp_assoc.
  now rewrite (@power_fmap_ev (C^op) HC J a a' h j).
Qed.

Definition cop_nat_pointwise (p : C^op ∏ C) :
  IsIsomorphism (transform[cop_nat] p) :=
  @Build_IsIsomorphism Sets _ _ _
    (from (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p)))
    (iso_to_from (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p)))
    (iso_from_to (copower_hom_iso_at (@copower_ump C HC J (fst p)) (snd p))).

Definition Copower_Bifunctor_Iso :
  @Isomorphism ([C^op ∏ C, Sets]) CopLeft CopRight :=
  @IsIsoToIso ([C^op ∏ C, Sets]) _ _ cop_nat
    (componentwise_iso cop_nat cop_nat_pointwise).

End ObjectParameterUnrestricted.

Arguments CopLeft {C HC} J.
Arguments CopRight {C} J.
Arguments Copower_Bifunctor_Iso {C HC} J.

(** ** D2. Mac Lane §IV.7 Exercise 1, PACKAGED as an adjunction with a
    parameter -- and the punchline, that the assembled right adjoint IS the
    hom-functor

    The packaging needs the right adjoint [C(a,−)] to land in the SAME index
    category the copower is indexed by, and there the two demands pull
    against each other: the copower wants LEIBNIZ equality on the index, the
    hom-functor wants [C]'s own [≈].  [HomAllStrict C] is exactly the
    hypothesis under which they coincide, and it is disclosed as an explicit
    argument rather than hidden.  It is inhabited in tree -- degenerately,
    by the terminal category, whose hom-setoid IS [Morphism_equality]. *)

(* [Construction/Comma/Special.v] already declares this hypothesis at a
   FIXED pair of objects, for exactly this reason (its [Full] criterion for
   the discrete-hom comparison), so it is CONSUMED here and quantified over
   all objects rather than redeclared.  Its [Blur_HomStrict_absurd] is a
   compiled witness of a category where the per-hom-set form is refutable. *)
Definition HomAllStrict (C : Category) : Type :=
  ∀ x y : C, @HomStrict C x y.

Section ObjectParameterPackaged.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (HS : HomAllStrict C).

Program Definition HomCoq (a : C) : C ⟶ Coq := {|
  fobj := fun c => @hom C a c ;
  fmap := fun c c' (k : c ~> c') => fun h : a ~> c => k ∘ h
|}.
Next Obligation. intros a c c' k k' Hk h; now rewrite (HS _ _ _ _ Hk). Qed.
Next Obligation. intros a c h; apply HS; apply id_left. Qed.
Next Obligation.
  intros a x y z k k' h; apply HS; simpl; symmetry; apply comp_assoc.
Qed.

(* The SAME bifunctor as §D0, with its two arguments exchanged so that the
   OBJECT sits in the parameter slot [P] of [ParametrizedAdjunction]. *)
Definition Ex1_Bifunctor : Coq ∏ C ⟶ C := Copower_Bifunctor ◯ Swap.

Example ex1_bifunctor_obj (J : Type) (a : C) :
  fobj[Ex1_Bifunctor] (J, a) = copower J a := eq_refl.

Example ex1_partial_obj (a : C) (J : Type) :
  fobj[Partial_l Ex1_Bifunctor a] J = copower J a := eq_refl.

Lemma ex1_partial_inj (a : C) {J J' : Type} (h : J ~{Coq}~> J') (j : J) :
  fmap[Partial_l Ex1_Bifunctor a] h ∘ copower_inj J a j
    ≈ copower_inj J' a (h j) ∘ id.
Proof.
  unfold Partial_l, Ex1_Bifunctor; simpl; unfold bimap; simpl.
  exact (cop_bifun_inj (a, J) (a, J') (id, h) j).
Qed.

Program Definition ex1_adj_iso (a : C) (J : Type) (c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Ex1_Bifunctor a] J) c
     ; is_setoid := @homset C (fobj[Partial_l Ex1_Bifunctor a] J) c |}
    {| carrier := @hom Coq J (fobj[HomCoq a] c)
     ; is_setoid := @homset Coq J (fobj[HomCoq a] c) |} :=
  {| to   := {| morphism := fun u => fun j : J => u ∘ copower_inj J a j |}
   ; from := {| morphism := fun fam : J → (a ~> c) =>
                  unique_obj (copower_desc (copower_ump J a) fam) |} |}.
Next Obligation. intros a J c u u' Hu j; apply HS; now rewrite Hu. Qed.
Next Obligation.
  intros a J c fam fam' Hfam.
  apply (uniqueness (copower_desc (copower_ump J a) fam)).
  intros j.
  rewrite (unique_property (copower_desc (copower_ump J a) fam') j).
  now rewrite (Hfam j).
Qed.
Next Obligation.
  intros a J c fam j; simpl.
  apply HS.
  exact (unique_property (copower_desc (copower_ump J a) fam) j).
Qed.
Next Obligation.
  intros a J c u; simpl.
  apply (uniqueness (copower_desc (copower_ump J a)
                       (fun j : J => u ∘ copower_inj J a j))).
  intros j; reflexivity.
Qed.

Example ex1_to_char (a : C) (J : Type) (c : C)
  (u : copower J a ~> c) (j : J) :
  to (ex1_adj_iso a J c) u j = u ∘ copower_inj J a j := eq_refl.

Definition ex1_pa_adj (a : C) : Partial_l Ex1_Bifunctor a ⊣ HomCoq a.
Proof.
  unshelve eapply (@Build_Adjunction' C Coq (Partial_l Ex1_Bifunctor a)
                     (HomCoq a) (ex1_adj_iso a)).
  - intros x y z f g j; simpl.
    apply HS.
    rewrite <- comp_assoc.
    rewrite (ex1_partial_inj a g j).
    now rewrite id_right.
  - intros x y z f g j; simpl.
    apply HS; symmetry; apply comp_assoc.
Defined.

Definition Copower_Object_ParametrizedAdjunction :
  ParametrizedAdjunction Ex1_Bifunctor := {|
  pa_right := HomCoq ;
  pa_adj   := ex1_pa_adj
|}.

(* ★ THE PUNCHLINE.  #396's Theorem 3 assembles the right adjoints into a
   bifunctor contravariant in the parameter, and that bifunctor IS the
   hom-functor of [C] -- on objects definitionally, on arrows pointwise. *)
Definition MacLane_Ex1_hom_bifunctor : C^op ∏ C ⟶ Coq :=
  @parametrized_right_adjoint_bifunctor Coq C C Ex1_Bifunctor
    Copower_Object_ParametrizedAdjunction.

Example ex1_hom_bifunctor_obj (a c : C) :
  fobj[MacLane_Ex1_hom_bifunctor] (a, c) = (a ~{C}~> c) := eq_refl.

Example ex1_pa_right_is_HomCoq (a : C) :
  pa_right Copower_Object_ParametrizedAdjunction a = HomCoq a := eq_refl.

Lemma ex1_counit_inj (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq a) (ex1_pa_adj a) c
    ∘ copower_inj (a ~> c) a g ≈ g.
Proof.
  exact (unique_property
           (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g).
Qed.

(* The parameter mate is PRECOMPOSITION -- read off [conj_mate]'s own
   component formula, not recomputed. *)
Lemma ex1_param_mate_precomp {a a' : C} (h : a' ~> a) (c : C)
  (g : a ~> c) :
  pa_param_mate Copower_Object_ParametrizedAdjunction h c g = g ∘ h.
Proof.
  unfold pa_param_mate, conj_mate; simpl.
  apply HS.
  rewrite <- comp_assoc.
  rewrite (cop_bifun_inj (a', (a ~> c)) (a, (a ~> c)) (h, id) g).
  simpl.
  rewrite comp_assoc.
  apply compose_respects; [ apply ex1_counit_inj | reflexivity ].
Qed.

Lemma ex1_hom_bifunctor_fmap {a a' c c' : C}
  (h : a ~{C^op}~> a') (k : c ~> c') (g : a ~> c) :
  fmap[MacLane_Ex1_hom_bifunctor] ((h, k) : (a, c) ~{C^op ∏ C}~> (a', c'))
    g = k ∘ g ∘ unop h.
Proof.
  etransitivity.
  { apply (f_equal (fun x : a' ~> c => k ∘ x)).
    exact (ex1_param_mate_precomp (unop h) c g). }
  apply HS; apply comp_assoc.
Qed.

End ObjectParameterPackaged.

Arguments HomCoq {C} HS a.
Arguments Ex1_Bifunctor {C HC}.

(* ** [HomAllStrict] is inhabited in tree, degenerately

   [_1]'s hom-setoid IS [Morphism_equality] (Instance/One.v), so
   [HomAllStrict _1] is the identity implication -- which is also the donor's
   own [One_HomStrict] (Construction/Comma/Special.v), there at the
   single object pair.  The witness exercises the
   HYPOTHESES and the assembly, not the conclusion: everything in [1]
   collapses to [ttt]. *)

Definition One_HomAllStrict : HomAllStrict _1 := fun _ _ _ _ H => H.

Lemma one_hom_eq {x y : _1} (f g : x ~{_1}~> y) : f = g.
Proof. destruct f, g; reflexivity. Qed.

Definition One_iprod_ump {A : Type} (f : A → _1) :
  IsIndexedProduct f ttt (fun _ => ttt).
Proof.
  constructor; intros c pi.
  exists ttt.
  - intros a; apply one_hom_eq.
  - intros v Hv; apply one_hom_eq.
Defined.

Definition One_icoprod_ump {A : Type} (f : A → _1) :
  @IsIndexedCoproduct _1 A f ttt (fun _ => ttt).
Proof.
  constructor; intros c pi.
  exists ttt.
  - intros a; apply one_hom_eq.
  - intros v Hv; apply one_hom_eq.
Defined.

Definition One_HasIndexedProducts : @HasIndexedProducts _1 :=
  @Build_HasIndexedProducts _1 (fun A f => ttt) (fun A f a => ttt)
    (@One_iprod_ump).

Definition One_HasIndexedCoproducts : @HasIndexedCoproducts _1 :=
  @Build_HasIndexedCoproducts _1 (fun A f => ttt) (fun A f a => ttt)
    (@One_icoprod_ump).

Definition One_Ex1_ParametrizedAdjunction :
  ParametrizedAdjunction (@Ex1_Bifunctor _1 One_HasIndexedCoproducts) :=
  @Copower_Object_ParametrizedAdjunction _1 One_HasIndexedCoproducts
    One_HomAllStrict.

(** ** E. The issue's own item 4: the INDEX SET as the parameter

    Here the parameter slot of [ParametrizedAdjunction] holds the index and
    the varying argument is the object, so the partial functors ARE §A's
    copower functors and the right adjoints ARE §A's power functors.  A
    function between index sets induces a transformation of copower functors
    whose CONJUGATE is the induced transformation of power functors, and
    that conjugacy is #396's [pa_natural_p] consumed, not recomputed. *)

Section IndexParameter.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.

(* The §B isomorphism ASCRIBES at the partial functor (both [fobj]s reduce
   to [copower J b]); the §B ADJUNCTION does not, because [Adjunction] is
   indexed by the functor RECORD.  Both facts are pinned in the probe. *)
Definition cp_pa_iso (J : Type) (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Copower_Bifunctor J] b) c
     ; is_setoid := @homset C (fobj[Partial_l Copower_Bifunctor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  cp_adj_iso J b c.

Lemma cp_partial_inj (J : Type) {b b' : C} (g : b ~> b') (j : J) :
  fmap[Partial_l Copower_Bifunctor J] g ∘ copower_inj J b j
    ≈ copower_inj J b' j ∘ g.
Proof.
  unfold Partial_l; simpl; unfold bimap; simpl.
  now rewrite (cop_bifun_inj (b, J) (b', J) (g, id) j).
Qed.

(* [cp_to_char] restated in the spelling these goals present: [rewrite] is
   syntactic and will not see through the [cp_pa_iso] delta. *)
Lemma cp_pa_char (J : Type) (b c : C) (u : copower J b ~> c) (j : J) :
  power_ev J c j ∘ to (cp_pa_iso J b c) u ≈ u ∘ copower_inj J b j.
Proof. exact (cp_to_char J b c u j). Qed.

Definition cp_pa_adj (J : Type) :
  Partial_l Copower_Bifunctor J ⊣ Power_Functor J.
Proof.
  unshelve eapply (Build_Adjunction' (cp_pa_iso J)).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc, cp_pa_char.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    symmetry; exact (cp_partial_inj J g j).
  - intros x y z f g.
    apply cp_to_uniq; intros j.
    rewrite comp_assoc.
    rewrite (power_functor_ev J f j).
    rewrite <- !comp_assoc; now rewrite (cp_pa_char J x y g j).
Defined.

Definition Copower_ParametrizedAdjunction :
  ParametrizedAdjunction Copower_Bifunctor := {|
  pa_right := fun J : Coq => Power_Functor J;
  pa_adj   := cp_pa_adj
|}.

Definition Power_Bifunctor : Coq^op ∏ C ⟶ C :=
  @parametrized_right_adjoint_bifunctor C Coq C Copower_Bifunctor
    Copower_ParametrizedAdjunction.

Example power_bifunctor_obj (J : Type) (b : C) :
  fobj[Power_Bifunctor] (J, b) = power J b := eq_refl.

Example pa_right_is_power_functor (J : Type) :
  pa_right Copower_ParametrizedAdjunction J = Power_Functor J := eq_refl.

(* The parametrized adjunction's own hom-set isomorphism at each index IS
   §B's, on the nose -- so §E does not fork §B's bijection. *)
Example pa_adj_iso_is_cp_adj_iso (J : Type) (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    (pa_adj Copower_ParametrizedAdjunction J) b c
  = cp_adj_iso J b c := eq_refl.

End IndexParameter.

Arguments cp_pa_adj {C HP HC} J.
Arguments Copower_ParametrizedAdjunction {C HP HC}.
Arguments Power_Bifunctor {C HP HC}.

Section IndexReindexing.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.

Notation PA := (@Copower_ParametrizedAdjunction C HP HC).
Notation CB := (@Copower_Bifunctor C HC).

(* Reindexing the COPOWER, covariantly in the index set. *)
Definition copower_reindex {J J' : Type} (h : J ~{Coq}~> J') :
  Partial_l CB J ⟹ Partial_l CB J' := param_transform CB h.

Lemma copower_reindex_inj {J J' : Type} (h : J ~{Coq}~> J') (b : C) (j : J) :
  copower_reindex h b ∘ copower_inj J b j ≈ copower_inj J' b (h j) ∘ id.
Proof. exact (cop_bifun_inj (b, J) (b, J') (id, h) j). Qed.

(* Reindexing the POWER, CONTRAVARIANTLY: #396's conjugate mate, consumed. *)
Definition power_reindex {J J' : Type} (h : J' ~{Coq}~> J) :
  Power_Functor J ⟹ Power_Functor J' := pa_param_mate PA h.

Example power_reindex_is_conj_mate {J J' : Type} (h : J' ~{Coq}~> J) :
  power_reindex h
    = conj_mate (pa_adj PA J) (pa_adj PA J') (param_transform CB h) := eq_refl.

(* The counit of the parametrized adjunction at the index [J], read through
   the copower injections: it IS the evaluation, with one identity residue. *)
Lemma cp_pa_counit_inj (J : Type) (b : C) (j : J) :
  @counit C C (Partial_l CB J) (Power_Functor J) (pa_adj PA J) b
    ∘ copower_inj J (power J b) j ≈ power_ev J b j.
Proof.
  etransitivity.
  - exact (unique_property
             (copower_desc (copower_ump J (power J b))
                (fun i : J => power_ev J b i ∘ id)) j).
  - apply id_right.
Qed.

(* The contravariant reindexing of powers is evaluation at [h j']. *)
Lemma power_reindex_ev {J J' : Type} (h : J' ~{Coq}~> J) (b : C) (j' : J') :
  power_ev J' b j' ∘ power_reindex h b ≈ power_ev J b (h j').
Proof.
  unfold power_reindex, pa_param_mate, conj_mate; simpl.
  etransitivity.
  { exact (unique_property (power_desc (power_ump J' b) _) j'). }
  rewrite <- comp_assoc.
  rewrite (copower_reindex_inj h (power J b) j').
  rewrite id_right.
  apply cp_pa_counit_inj.
Qed.

(* ★ THE CONJUGACY, CONSUMED.  [pa_natural_p] is #396's theorem and
   [pa_square_is_Conjugate] says the square IS #394's [Conjugate] on the
   nose, so the ascription below is the whole proof. *)
Definition power_reindex_conjugate {J J' : Type} (h : J' ~{Coq}~> J) :
  Conjugate (pa_adj PA J) (pa_adj PA J')
            (copower_reindex h) (power_reindex h) :=
  pa_natural_p PA h.

(* And it is the UNIQUE such transformation. *)
Definition power_reindex_universal {J J' : Type} (h : J' ~{Coq}~> J) :
  ∃! tau : Power_Functor J ⟹ Power_Functor J',
    Conjugate (pa_adj PA J) (pa_adj PA J') (copower_reindex h) tau :=
  pa_param_mate_universal PA h.

Corollary power_reindex_id (J : Type) : power_reindex (@id Coq J) ≈ nat_id.
Proof. exact (pa_param_mate_id PA). Qed.

Corollary power_reindex_comp {J J' J'' : Type}
  (h : J' ~{Coq}~> J) (h' : J'' ~{Coq}~> J') :
  power_reindex (h ∘ h') ≈ power_reindex h' ∙ power_reindex h.
Proof. exact (pa_param_mate_comp PA h h'). Qed.

Corollary copower_reindex_id (J : Type) :
  copower_reindex (@id Coq J) ≈ nat_id.
Proof. exact (param_transform_id CB). Qed.

Corollary copower_reindex_comp {J J' J'' : Type}
  (h : J ~{Coq}~> J') (h' : J' ~{Coq}~> J'') :
  copower_reindex (h' ∘ h) ≈ copower_reindex h' ∙ copower_reindex h.
Proof. exact (param_transform_comp CB h h'). Qed.

End IndexReindexing.
