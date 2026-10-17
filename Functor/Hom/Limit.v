Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Continuity of the covariant hom-functor *)

(*
   nLab:      https://ncatlab.org/nlab/show/continuous+functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The covariant hom-functor preserves limit cones *)

Section HomContinuous.

Context {C : Category}.
Context (c : C).

Definition HomFrom : C ⟶ Sets := [Hom c ,─].

(* An element of the apex of a cone over [Hom c,─] ◯ K is itself a cone
   over K with apex c: its legs are the legs of M read at that element,
   and its coherence is M's coherence read there. *)

Section Fibre.

Context {J : Category}.
Context {K : J ⟶ C}.
Context (M : Cone (HomFrom ◯ K)).

Lemma hom_fibre_coherence (s : vertex_obj[M]) {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ cone_leg M x s ≈ cone_leg M y s.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f s).
Qed.

Definition hom_fibre_cone (s : vertex_obj[M]) : Cone K :=
  @Build_Cone J C K c
    (@Build_ACone J C c K (fun x => cone_leg M x s)
       (fun x y f => hom_fibre_coherence s f)).

End Fibre.

(* The mediating map of Sets: it sends an element to the mediator its
   fibre cone determines.  Respectfulness is not an extra hypothesis --
   it follows from uniqueness of the mediator, since [≈]-equal elements
   give fibre cones with [≈]-equal legs. *)

Section Mediator.

Context {J : Category}.
Context {K : J ⟶ C}.
Context {N : Cone K}.
Context (HN : IsLimitCone N).
Context (M : Cone (HomFrom ◯ K)).

Definition hom_med_fun (s : vertex_obj[M]) : c ~{C}~> vertex_obj[N] :=
  unique_obj (HN (hom_fibre_cone M s)).

Lemma hom_med_commutes (s : vertex_obj[M]) (x : J) :
  cone_leg N x ∘ hom_med_fun s ≈ cone_leg M x s.
Proof. exact (unique_property (HN (hom_fibre_cone M s)) x). Qed.

Lemma hom_med_unique (s : vertex_obj[M]) (v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, cone_leg N x ∘ v ≈ cone_leg M x s) → hom_med_fun s ≈ v.
Proof. intro Hv. exact (uniqueness (HN (hom_fibre_cone M s)) v Hv). Qed.

#[local] Instance hom_med_respects : Proper (equiv ==> equiv) hom_med_fun.
Proof.
  intros s t Hst.
  apply hom_med_unique.
  intro x.
  rewrite hom_med_commutes.
  now rewrite Hst.
Qed.

Definition hom_med : vertex_obj[M] ~{Sets}~> fobj[HomFrom] (vertex_obj[N]) :=
  {| morphism := hom_med_fun ; proper_morphism := hom_med_respects |}.

End Mediator.

(* The headline, per diagram and then over all shapes at once. *)

Definition hom_PreservesLimitCone {J : Category} (K : J ⟶ C) :
  PreservesLimitCone K HomFrom.
Proof.
  intros N HN M.
  unshelve refine {| unique_obj := hom_med HN M |}.
  - simpl; intros x s.
    exact (hom_med_commutes HN M s x).
  - simpl; intros v Hv s.
    apply hom_med_unique.
    intro x.
    exact (Hv x s).
Defined.

Definition hom_ContinuousFunctor : ContinuousFunctor HomFrom :=
  fun J K => hom_PreservesLimitCone K.

(* The apex-only readings, through the donor's own bridges.  These are
   WEAKER: they name no legs and no mediator.  Whether they are strictly
   weaker for this particular functor is not settled here. *)

Definition hom_PreservesLimit {J : Category} (K : J ⟶ C) :
  PreservesLimit K HomFrom :=
  PreservesLimitCone_PreservesLimit (hom_PreservesLimitCone K).

Definition hom_PreservesAllLimits : PreservesAllLimits HomFrom :=
  Continuous_PreservesAllLimits hom_ContinuousFunctor.

(* What the cone level pins down, and the apex-only reading does not. *)

Example hom_preserved_leg {J : Category} {K : J ⟶ C} (N : Cone K) (x : J) :
  cone_leg (FCone HomFrom N) x = fmap[HomFrom] (cone_leg N x) := eq_refl.

Lemma hom_preserved_leg_value {J : Category} {K : J ⟶ C} (N : Cone K)
  (x : J) (h : c ~{C}~> vertex_obj[N]) :
  cone_leg (FCone HomFrom N) x h ≈ cone_leg N x ∘ h.
Proof. reflexivity. Qed.

Example hom_preserved_mediator {J : Category} {K : J ⟶ C} {N : Cone K}
  (HN : IsLimitCone N) (M : Cone (HomFrom ◯ K)) :
  unique_obj (hom_PreservesLimitCone K N HN M) = hom_med HN M := eq_refl.

(** ** Mac Lane's own case: products *)

(* Indexed products, at the elementary record of Structure/Limit/Product.v
   and for an arbitrary index [Type].  Proved directly; the header
   records the measured universe cost of routing this through the
   discrete-diagram presentation instead. *)

Section IndexedProducts.

Context {A : Type}.
Context {f : A → C}.
Context {p : C}.
Context {proj : ∀ a : A, p ~{C}~> f a}.
Context (H : IsIndexedProduct f p proj).

Section Fixed.

Context {S : Sets}.
Context (pi : ∀ a : A, S ~{Sets}~> fobj[HomFrom] (f a)).

Definition hom_iprod_med_fun (s : S) : c ~{C}~> p :=
  unique_obj (iprod_desc H (fun a => pi a s)).

Lemma hom_iprod_med_commutes (s : S) (a : A) :
  proj a ∘ hom_iprod_med_fun s ≈ pi a s.
Proof. exact (unique_property (iprod_desc H (fun a => pi a s)) a). Qed.

Lemma hom_iprod_med_unique (s : S) (v : c ~{C}~> p) :
  (∀ a : A, proj a ∘ v ≈ pi a s) → hom_iprod_med_fun s ≈ v.
Proof. intro Hv. exact (uniqueness (iprod_desc H (fun a => pi a s)) v Hv). Qed.

#[local] Instance hom_iprod_med_respects :
  Proper (equiv ==> equiv) hom_iprod_med_fun.
Proof.
  intros s t Hst.
  apply hom_iprod_med_unique.
  intro a.
  rewrite hom_iprod_med_commutes.
  now rewrite Hst.
Qed.

Definition hom_iprod_med : S ~{Sets}~> fobj[HomFrom] p :=
  {| morphism := hom_iprod_med_fun ;
     proper_morphism := hom_iprod_med_respects |}.

End Fixed.

Definition hom_IsIndexedProduct :
  @IsIndexedProduct Sets A (fun a => fobj[HomFrom] (f a))
    (fobj[HomFrom] p) (fun a => fmap[HomFrom] (proj a)).
Proof using H.
  constructor.
  intros S pi.
  unshelve refine {| unique_obj := hom_iprod_med pi |}.
  - simpl; intros a s.
    exact (hom_iprod_med_commutes pi s a).
  - simpl; intros v Hv s.
    apply hom_iprod_med_unique.
    intro a.
    exact (Hv a s).
Defined.

End IndexedProducts.

(* The binary case, at the apex-pinned [IsCartesianProduct]: the
   conclusion is that [C(c, z)] is a product of [C(c, x)] and [C(c, y)]
   in Sets, with post-composition as the two projections. *)

Section BinaryProducts.

Context {x y z : C}.
Context (H : @IsCartesianProduct C x y z).

Definition hom_fork_fun {S : Sets} (F : S ~{Sets}~> fobj[HomFrom] x)
  (G : S ~{Sets}~> fobj[HomFrom] y) (s : S) : c ~{C}~> z :=
  @fork' C x y z H c (F s) (G s).

#[local] Instance hom_fork_respects {S : Sets}
  (F : S ~{Sets}~> fobj[HomFrom] x) (G : S ~{Sets}~> fobj[HomFrom] y) :
  Proper (equiv ==> equiv) (hom_fork_fun F G).
Proof.
  intros s t Hst; unfold hom_fork_fun.
  apply fork'_respects; now rewrite Hst.
Qed.

Definition hom_fork {S : Sets} (F : S ~{Sets}~> fobj[HomFrom] x)
  (G : S ~{Sets}~> fobj[HomFrom] y) : S ~{Sets}~> fobj[HomFrom] z :=
  {| morphism := hom_fork_fun F G ;
     proper_morphism := hom_fork_respects F G |}.

Definition hom_IsCartesianProduct :
  @IsCartesianProduct Sets (fobj[HomFrom] x) (fobj[HomFrom] y)
    (fobj[HomFrom] z).
Proof using H.
  unshelve refine {| fork' := fun S F G => hom_fork F G ;
                     exl' := fmap[HomFrom] (@exl' C x y z H) ;
                     exr' := fmap[HomFrom] (@exr' C x y z H) |}.
  - intros S F F' HF G G' HG s; simpl.
    unfold hom_fork_fun.
    apply fork'_respects; [ exact (HF s) | exact (HG s) ].
  - simpl; intros S F G h.
    split.
    + intro Hh.
      split; intro s.
      * exact (fst (fst (@ump_product C x y z H c (F s) (G s) (h s)) (Hh s))).
      * exact (snd (fst (@ump_product C x y z H c (F s) (G s) (h s)) (Hh s))).
    + intros [Hl Hr] s.
      exact (snd (@ump_product C x y z H c (F s) (G s) (h s))
               (Hl s, Hr s)).
Defined.

End BinaryProducts.

End HomContinuous.

(** ** The contravariant twin: colimits of C become limits of Sets *)

(* [Hom ─,c] IS the covariant hom-functor of C^op, definitionally, so
   every constant here is instantiation: all are supplied by [:=] with
   no tactic. *)

Section HomContravariant.

Context {C : Category}.
Context (c : C).

Definition HomTo : C^op ⟶ Sets := [Hom ─, c].

Example hom_to_is_op_hom_from : HomTo = @HomFrom (C^op) c := eq_refl.

Definition cohom_ContinuousFunctor : ContinuousFunctor HomTo :=
  @hom_ContinuousFunctor (C^op) c.

Definition cohom_PreservesLimitCone {J : Category} (K : J ⟶ C^op) :
  PreservesLimitCone K HomTo := @hom_PreservesLimitCone (C^op) c J K.

(* The covariant reading in C: a colimiting cocone of C is carried to a
   limiting cone of Sets.  [Cocone K] is [Cone (K^op)] and
   [IsColimitCocone] is [IsLimitCone] at the opposite diagram, so no
   repackaging is needed. *)

Definition cohom_colimit_to_limit {J : Category} {K : J ⟶ C}
  (N : Cocone K) (HN : IsColimitCocone N) : IsLimitCone (FCone HomTo N) :=
  cohom_PreservesLimitCone (Opposite_Functor K) N HN.

(* Coproducts of C become products in Sets; the projections are
   PREcomposition with the injections.  DISPLAY HAZARD: [Check] prints
   the hypothesis of [cohom_IsCartesianProduct] as
   [IsCartesianProduct x y z] with the category argument suppressed, so
   the printed type reads as though the product were taken in C.  It is
   not: the source spells [@IsCartesianProduct (C^op) x y z], i.e. z is
   the COPRODUCT of x and y in C. *)

Definition cohom_IsIndexedProduct {A : Type} {g : A → C} {q : C}
  {inj : ∀ a : A, g a ~{C}~> q} (H : IsIndexedCoproduct g q inj) :
  @IsIndexedProduct Sets A (fun a => fobj[HomTo] (g a)) (fobj[HomTo] q)
    (fun a => fmap[HomTo] (inj a)) :=
  @hom_IsIndexedProduct (C^op) c A g q inj H.

Definition cohom_IsCartesianProduct {x y z : C}
  (H : @IsCartesianProduct (C^op) x y z) :
  @IsCartesianProduct Sets (fobj[HomTo] x) (fobj[HomTo] y) (fobj[HomTo] z) :=
  @hom_IsCartesianProduct (C^op) c x y z H.

End HomContravariant.

(** ** Non-vacuity *)

(* The repackaging Structure/Cartesian.v does not carry: a bundled
   [Cartesian] structure read at one chosen pair as an apex-pinned
   product.  Supplied here only to state the witness below; deliberately
   not registered as an [Instance]. *)

Program Definition cartesian_IsCartesianProduct {C : Category}
  `{@Cartesian C} (x y : C) : IsCartesianProduct x y (x × y) := {|
  fork' := fun _ f g => f △ g ;
  exl'  := exl ;
  exr'  := exr
|}.
Next Obligation. apply ump_products. Qed.

(* Witness (1): the binary product corollary at [Coq_Cartesian].  The
   three Examples below compute by [eq_refl]. *)

Definition coq_hom_product (u x y : Coq) :
  @IsCartesianProduct Sets (fobj[HomFrom u] x) (fobj[HomFrom u] y)
    (fobj[HomFrom u] (x × y)%object) :=
  hom_IsCartesianProduct u (cartesian_IsCartesianProduct x y).

Definition coq_hp := coq_hom_product unit bool nat.

Example coq_hom_exl_computes :
  @exl' Sets _ _ _ coq_hp (fun _ : unit => (true, 3%nat)) tt = true := eq_refl.

Example coq_hom_exr_computes :
  @exr' Sets _ _ _ coq_hp (fun _ : unit => (true, 3%nat)) tt = 3%nat := eq_refl.

Example coq_hom_fork_computes :
  @fork' Sets _ _ _ coq_hp _ (@exl' Sets _ _ _ coq_hp)
    (@exr' Sets _ _ _ coq_hp) (fun _ : unit => (true, 3%nat)) tt
    = (true, 3%nat) := eq_refl.

(* Witness (2): the CONE-LEVEL headline at an in-tree limit -- the one
   [Cartesian_Limit] produces from [Coq_Cartesian].  It does not compute
   ([Cartesian_Limit] is [Qed]) and its ambient category is measurably
   [Coq@{u1 Set Set}], for the reason the header analyses. *)

Definition coq_two_limit (F : Two_Discrete ⟶ Coq) : Limit F :=
  snd (Cartesian_Limit Coq) Coq_Cartesian F.

Definition coq_hom_limit_cone (u : Coq) (F : Two_Discrete ⟶ Coq) :
  IsLimitCone (FCone (HomFrom u) (@limit_cone _ _ _ (coq_two_limit F))) :=
  hom_PreservesLimitCone u F _ (limit_limitcone (coq_two_limit F)).

Definition coq_hom_bool_nat_limit :
  IsLimitCone (@FCone Two_Discrete Coq Sets (HomFrom unit)
                 (Pick_Two bool nat)
                 (coq_two_limit (Pick_Two bool nat))) :=
  coq_hom_limit_cone unit (Pick_Two bool nat).
