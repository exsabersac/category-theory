Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.

Generalizable All Variables.

(** * Colimits of spaces: the final topology, and [PTopCat] cocomplete *)

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/initial+topology
 nLab: https://ncatlab.org/nlab/show/quotient+space
 nLab: https://ncatlab.org/nlab/show/topological+concrete+category
 nLab: https://ncatlab.org/nlab/show/cocomplete+category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** The final topology of a family of maps into a setoid *)

Section Final.

Universes o i.

Context (S : SetoidObject@{o o}) (Ix : Type@{i}) (X : Ix → PTop@{o})
        (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S).

(* A predicate on [S] is open when it respects the equality of [S] and its
   preimage along every [f k] is open. *)
Definition pfinal_open (V : S → Prop) : Prop :=
  (∀ s t : S, s ≈ t → V s → V t) /\
  (∀ k : Ix, POpen (X k) (fun x => V (f k x))).

Lemma pfinal_open_respects (U V : S → Prop) :
  (∀ s, U s <-> V s) → pfinal_open U → pfinal_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros s t e v. apply (proj1 (H t)), (Hp s t e), (proj2 (H s)), v.
  - intro k. exact (popen_respects (X k) _ _ (fun x => H (f k x)) (Ho k)).
Qed.

Lemma pfinal_open_proper (U : S → Prop) :
  pfinal_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma pfinal_open_union (F : (S → Prop) → Prop) :
  (∀ V, F V → pfinal_open V) →
  pfinal_open (fun s => ex (fun V => F V /\ V s)).
Proof.
  intro HF; split.
  - intros s t e [V [FV v]]. exists V; split; [exact FV|].
    exact (proj1 (HF V FV) s t e v).
  - intro k.
    apply (popen_respects (X k)
             (fun x => ex (fun U => ex (fun V => F V /\
                                          ∀ y, U y <-> V (f k y)) /\ U x))).
    + intro x; split.
      * intros [U [[V [FV HUV]] u]]. exists V.
        split; [exact FV|exact (proj1 (HUV x) u)].
      * intros [V [FV v]]. exists (fun y => V (f k y)).
        split; [|exact v]. exists V; split; [exact FV|].
        intro y; exact (iff_refl _).
    + apply popen_union. intros U [V [FV HUV]].
      apply (popen_respects (X k) (fun y => V (f k y))).
      * intro y; exact (iff_sym (HUV y)).
      * exact (proj2 (HF V FV) k).
Qed.

Lemma pfinal_open_whole : pfinal_open (fun _ => True).
Proof. split; [intros; exact I|intro k; exact (popen_whole (X k))]. Qed.

Lemma pfinal_open_inter (U V : S → Prop) :
  pfinal_open U → pfinal_open V → pfinal_open (fun s => U s /\ V s).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros s t e [u v]; exact (conj (HpU s t e u) (HpV s t e v)).
  - intro k; exact (popen_inter (X k) _ _ (HoU k) (HoV k)).
Qed.

(* A record literal over the five lemmas, so that the points and the opens
   read back at [eq_refl]. *)
Definition PFinal : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pfinal_open;
  popen_respects := pfinal_open_respects;
  popen_proper   := pfinal_open_proper;
  popen_union    := pfinal_open_union;
  popen_whole    := pfinal_open_whole;
  popen_inter    := pfinal_open_inter
|}.

Example PFinal_carrier : pt_carrier PFinal = S := eq_refl.

Example PFinal_open (V : S → Prop) :
  POpen PFinal V
  = ((∀ s t : S, s ≈ t → V s → V t) /\
     (∀ k : Ix, POpen (X k) (fun x => V (f k x)))) := eq_refl.

Lemma pfinal_leg_cont (k : Ix) : @PCont (X k) PFinal (f k).
Proof. intros V HV; exact (proj2 HV k). Qed.

Definition pfinal_leg (k : Ix) : PMor@{o} (X k) PFinal :=
  @Build_PMor (X k) PFinal (f k) (pfinal_leg_cont k).

Example pfinal_leg_map (k : Ix) : pmap (pfinal_leg k) = f k := eq_refl.

(* The universal property, over ARBITRARY spaces [Z] mapping out: a setoid
   map out of [S] is continuous from the final topology exactly when its
   composite with every [f k] is continuous. *)
Lemma pfinal_universal (Z : PTop@{o}) (g : SetoidMorphism@{o o o} S Z) :
  @PCont PFinal Z g <->
  (∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))).
Proof.
  split.
  - intros Hg k W HW. exact (proj2 (Hg W HW) k).
  - intros Hc W HW; split.
    + intros s t e w.
      exact (popen_proper Z W HW (g s) (g t) (proper_morphism g s t e) w).
    + intro k; exact (Hc k W HW).
Qed.

(* The book's form of it: the map out of the final topology. *)
Definition pfinal_desc (Z : PTop@{o}) (g : SetoidMorphism@{o o o} S Z)
  (Hg : ∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :
  PMor@{o} PFinal Z :=
  @Build_PMor PFinal Z g (proj2 (pfinal_universal Z g) Hg).

Example pfinal_desc_map (Z : PTop@{o}) (g : SetoidMorphism@{o o o} S Z)
  (Hg : ∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :
  pmap (pfinal_desc Z g Hg) = g := eq_refl.

(* It is the FINEST topology making every [f k] continuous: any family of
   predicates on [S] respecting its equality, each with open preimages
   along every [f k], consists of opens of the final topology.  The family
   need not be a topology. *)
Lemma pfinal_finest (T : (S → Prop) → Prop)
  (Hp : ∀ U, T U → ∀ s t : S, s ≈ t → U s → U t)
  (Hc : ∀ U, T U → ∀ k, POpen (X k) (fun x => U (f k x))) :
  ∀ U, T U → POpen PFinal U.
Proof. intros U HU; exact (conj (Hp U HU) (Hc U HU)). Qed.

End Final.

(* The quotient topology of Instance/Top/Subspace.v is the one-map case:
   [PQuot X T q] and the final topology of the single map [q] have the
   same opens. *)
Lemma pfinal_one_map_PQuot@{o +} (X : PTop@{o}) (T : SetoidObject@{o o})
  (q : SetoidMorphism@{o o o} X T) (V : T → Prop) :
  POpen (PQuot X T q) V
  <-> POpen (PFinal T Datatypes.unit (fun _ => X) (fun _ => q)) V.
Proof.
  split.
  - intros [Hp Ho]; split; [exact Hp|intros _; exact Ho].
  - intros [Hp Ho]; split; [exact Hp|exact (Ho tt)].
Qed.

(** ** The recipe: the final topology on a colimit of the points *)

Section Recipe.

Universes o so s.
Constraint o < so.

Context {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}).

Local Notation G := (PForget@{o so} ◯ F).

Section OverACocone.

Context (N : Cocone G).

(* The final topology on the apex of [N] for its legs. *)
Definition pfinal_cocone_obj : PTop@{o} :=
  PFinal (vertex_obj[N]) (obj[D]) (fun d => F d) (fun d => cocone_inj N d).

Definition pfinal_cocone_inj (d : D) :
  F d ~{PTopCat@{o so}}~> pfinal_cocone_obj :=
  pfinal_leg _ _ _ _ d.

Program Definition PFinalCocone : Cocone F := {|
  vertex_obj := pfinal_cocone_obj;
  coneFrom   := {| vertex_map := pfinal_cocone_inj |}
|}.
Next Obligation.
  intros d d' g x.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' g x).
Qed.

(* The lifted cocone forgets to [N] on the nose: its image under [PForget]
   has [N]'s apex and [N]'s legs. *)
Example PFinalCocone_points :
  vertex_obj[FCocone PForget@{o so} PFinalCocone] = vertex_obj[N] := eq_refl.

Example PFinalCocone_legs (d : D) :
  cocone_inj (FCocone PForget@{o so} PFinalCocone) d = cocone_inj N d
  := eq_refl.

End OverACocone.

End Recipe.

(* THE RECIPE, as a lemma: if [N] is a colimiting cocone of the points,
   the final topology for its legs makes the lifted cocone colimiting.
   The two universal properties are stated at independent levels. *)
Lemma pfinal_cocone_colimiting@{o so s r r' x x' +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) :
  IsColimitCocone@{x x r s o so} (PFinalCocone F N).
Proof.
  intro M.
  pose proof (colimitcocone_ump HN (FCocone PForget@{o so} M)) as U.
  unshelve eapply Build_Unique.
  - refine (pfinal_desc _ _ _ _ (vertex_obj[M]) (unique_obj U) _).
    intro d.
    apply (pcont_respects (pmap (cocone_inj M d))).
    + intro x; symmetry; exact (unique_property U d x).
    + exact (pcont (cocone_inj M d)).
  - intros d x. exact (unique_property U d x).
  - intros v Hv x. simpl.
    exact (uniqueness U (pmap v) (fun d y => Hv d y) x).
Defined.

(* The mediator out of the lifted cocone IS the [Sets] mediator. *)
Example pfinal_cocone_med_map@{o so s r r' x x' +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) (M : Cocone F) :
  pmap (unique_obj (pfinal_cocone_colimiting@{o so s r r' x x' _} F N HN M))
    = unique_obj (colimitcocone_ump HN (FCocone PForget@{o so} M)) := eq_refl.

(* The recipe for a colimit record of the points.  The colimit of the
   points and the colimit of spaces are records at two levels, [r'] and
   [r], left independent. *)
Definition PTop_Colimit_lift@{r r' s o so +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (L : Colimit@{r' s o so} (PForget@{o so} ◯ F)) : Colimit@{r s o so} F :=
  limitcone_limit (PFinalCocone F (@limit_cone _ _ _ L))
    (pfinal_cocone_colimiting F _ (colimit_colimitcocone L)).

Example PTop_Colimit_lift_apex@{r r' s o so +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (L : Colimit@{r' s o so} (PForget@{o so} ◯ F)) :
  vertex_obj[@limit_cone _ _ _ (PTop_Colimit_lift@{r r' s o so _ _ _} F L)]
    = PFinal (vertex_obj[@limit_cone _ _ _ L]) (obj[D]) (fun d => F d)
        (fun d => cocone_inj (@limit_cone _ _ _ L) d) := eq_refl.

(** ** Remark 2 directly: the recipe at the colimit of [Sets] *)

Section PColimit.

Universes r s o so.
Constraint o < so.
Constraint s <= o.
Constraint o <= r.

Context {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}).

Local Notation G := (PForget@{o so} ◯ F).

Definition PColimit : Colimit@{r s o so} F :=
  PTop_Colimit_lift F (Sets_Colimit G).

Example PColimit_apex :
  vertex_obj[@limit_cone _ _ _ PColimit]
    = PFinal (Sets_colim_obj G) (obj[D]) (fun d => F d)
        (fun d => Sets_colim_inj G d) := eq_refl.

Example PColimit_points :
  pt_carrier (vertex_obj[@limit_cone _ _ _ PColimit]) = Sets_colim_obj G
  := eq_refl.

Example PColimit_inj (d : D) :
  pmap (cocone_inj (@limit_cone _ _ _ PColimit) d) = Sets_colim_inj G d
  := eq_refl.

(* The triangle, on the nose: the mediator into a cocone [M] sends the
   point [x] of the summand at [d] to [M]'s leg at [d] applied to [x], as
   Instance/Sets/Cocomplete.v's [Sets_colim_triangle] does for [Sets]. *)
Example PColimit_med_at (M : Cocone F) (d : D) (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ PColimit M)) (existT _ d x)
    = pmap (cocone_inj M d) x := eq_refl.

End PColimit.

Definition PTop_Cocomplete@{r s o so +| o < so, s <= o, o <= r +} :
  @Cocomplete@{r s o so} PTopCat@{o so} := fun D F => PColimit F.

(** ** Indexed coproducts: the final topology on the disjoint union *)

Section PSigma.

Universes o i.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → PTop@{o}).

(* The disjoint union of the points, [Sets_icoprod_obj], with the final
   topology for its injections. *)
Definition PSigma : PTop@{o} :=
  PFinal (Sets_icoprod_obj (fun k => pt_carrier (X k))) Ix X
    (fun k => Sets_icoprod_inj (fun k => pt_carrier (X k)) k).

Example PSigma_points :
  pt_carrier PSigma = Sets_icoprod_obj (fun k => pt_carrier (X k)) := eq_refl.

Example PSigma_open (V : Sets_icoprod_obj (fun k => pt_carrier (X k)) → Prop) :
  POpen PSigma V
  = ((∀ p q : Sets_icoprod_obj (fun k => pt_carrier (X k)),
        p ≈ q → V p → V q) /\
     (∀ k : Ix, POpen (X k) (fun x => V (existT _ k x)))) := eq_refl.

End PSigma.

Section PSigmaUMP.

Universes o so i.
Constraint o < so.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → PTopCat@{o so}).

Definition psigma_inj (k : Ix) : X k ~{PTopCat@{o so}}~> PSigma Ix X :=
  pfinal_leg _ _ _ _ k.

Definition psigma_case (Z : PTopCat@{o so})
  (iota : ∀ k, X k ~{PTopCat@{o so}}~> Z) :
  PSigma Ix X ~{PTopCat@{o so}}~> Z :=
  pfinal_desc _ Ix X (fun k => Sets_icoprod_inj (fun k => pt_carrier (X k)) k)
    Z (Sets_icoprod_case (fun k => pt_carrier (X k)) (pt_carrier Z)
         (fun k => pmap (iota k)))
    (fun k => pcont (iota k)).

Example psigma_case_at (Z : PTopCat@{o so})
  (iota : ∀ k, X k ~{PTopCat@{o so}}~> Z) (k : Ix) (x : X k) :
  pmap (psigma_case Z iota) (existT _ k x) = pmap (iota k) x := eq_refl.

Lemma psigma_desc (Z : PTopCat@{o so})
  (iota : ∀ k, X k ~{PTopCat@{o so}}~> Z) :
  ∃! u : PSigma Ix X ~{PTopCat@{o so}}~> Z, ∀ k, u ∘ psigma_inj k ≈ iota k.
Proof.
  unshelve eapply Build_Unique.
  - exact (psigma_case Z iota).
  - intros k x; reflexivity.
  - intros v Hv [k x]; simpl. symmetry. exact (Hv k x).
Defined.

Definition PTop_IsIndexedCoproduct :
  IsIndexedCoproduct X (PSigma Ix X) psigma_inj :=
  Build_IsIndexedCoproduct X _ _ (fun c iota => psigma_desc c iota).

End PSigmaUMP.

Definition PTop_HasIndexedCoproducts@{o so +| o < so +} :
  HasIndexedCoproducts PTopCat@{o so} :=
  @Build_HasIndexedCoproducts PTopCat@{o so}
    (fun A f => PSigma A f)
    (fun A f k => psigma_inj A f k)
    (fun A f => PTop_IsIndexedCoproduct A f).

(** ** Remark 2 by the book's route: coproducts and the dual of
       Proposition 1 *)

Definition PTop_Cocomplete_via_coproducts@{o so +| o < so +} :
  @Cocomplete PTopCat@{o so} :=
  Cocomplete_from_coproducts_coequalizers PTop_HasIndexedCoproducts
    PTop_HasCoequalizers.

(* The book-route colimit IS a quotient topology on a disjoint union: its
   apex is [PQuot] of [PSigma] of the diagram's spaces, along the
   projection onto a [Sets] coequalizer, on the nose. *)
Example PTop_Cocomplete_via_coproducts_apex@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  { A : SetoidObject@{o o} &
  { f : A ~{Sets@{o so}}~> pt_carrier (PSigma (obj[D]) (fun d => F d)) &
  { g : A ~{Sets@{o so}}~> pt_carrier (PSigma (obj[D]) (fun d => F d)) &
    vertex_obj[@limit_cone _ _ _ (PTop_Cocomplete_via_coproducts D F)]
      = PQuot (PSigma (obj[D]) (fun d => F d)) (SetsCoeq f g)
          (sets_coeq_proj f g) } } }.
Proof. eexists; eexists; eexists; reflexivity. Defined.

(* The two routes agree where both are stated, at shapes whose objects sit
   at the points' universe: the two apexes are isomorphic, compatibly with
   the injections (Structure/Limit/Unique.v's [colimit_unique_iso]). *)
Definition PTop_Cocomplete_routes_iso@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
    ≅[PTopCat@{o so}] colimit_apex (PTop_Cocomplete_via_coproducts D F) :=
  colimit_unique_iso (colimit_is_acolimit _) (colimit_is_acolimit _).

Lemma PTop_Cocomplete_routes_iso_injs@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) (d : D) :
  to (PTop_Cocomplete_routes_iso D F)
    ∘ colimit_inj (colimit_is_acolimit (PTop_Cocomplete D F)) d
  ≈ colimit_inj (colimit_is_acolimit (PTop_Cocomplete_via_coproducts D F)) d.
Proof. exact (fst (colimit_unique_iso_injs _ _) d). Qed.

(** ** The indiscrete topology, and the underlying-set functor as a left
       adjoint *)

Section Indiscrete.

Universe o.

Context (S : SetoidObject@{o o}).

(* The coarsest topology: the uniform predicates. *)
Definition pindisc_open (U : S → Prop) : Prop := ∀ x y : S, U x → U y.

Lemma pindisc_open_respects (U V : S → Prop) :
  (∀ x, U x <-> V x) → pindisc_open U → pindisc_open V.
Proof.
  intros H HU x y v. apply (proj1 (H y)), (HU x y), (proj2 (H x)), v.
Qed.

Lemma pindisc_open_proper (U : S → Prop) :
  pindisc_open U → ∀ x y : S, x ≈ y → U x → U y.
Proof. intros HU x y _; exact (HU x y). Qed.

Lemma pindisc_open_union (F : (S → Prop) → Prop) :
  (∀ U, F U → pindisc_open U) →
  pindisc_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x y [U [FU u]]. exists U; split; [exact FU|].
  exact (HF U FU x y u).
Qed.

Lemma pindisc_open_whole : pindisc_open (fun _ => True).
Proof. intros x y t; exact t. Qed.

Lemma pindisc_open_inter (U V : S → Prop) :
  pindisc_open U → pindisc_open V → pindisc_open (fun x => U x /\ V x).
Proof.
  intros HU HV x y [u v]; exact (conj (HU x y u) (HV x y v)).
Qed.

Definition PIndiscrete : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pindisc_open;
  popen_respects := pindisc_open_respects;
  popen_proper   := pindisc_open_proper;
  popen_union    := pindisc_open_union;
  popen_whole    := pindisc_open_whole;
  popen_inter    := pindisc_open_inter
|}.

Example PIndiscrete_carrier : pt_carrier PIndiscrete = S := eq_refl.

Example PIndiscrete_open (U : S → Prop) :
  POpen PIndiscrete U = (∀ x y : S, U x → U y) := eq_refl.

(* Every setoid map into an indiscrete space is continuous: the preimage of
   a uniform predicate is constant up to [<->], and constants are open
   (Instance/Top/Prop.v's [popen_const]). *)
Lemma pindisc_cont (X : PTop@{o}) (f : SetoidMorphism@{o o o} X S) :
  @PCont X PIndiscrete f.
Proof.
  intros U HU. apply (popen_respects X (fun _ => ex (fun x => U (f x)))).
  - intro x; split.
    + intros [y u]. exact (HU (f y) (f x) u).
    + intro u. exists x. exact u.
  - apply popen_const.
Qed.

Definition pindisc_mor (X : PTop@{o}) (f : SetoidMorphism@{o o o} X S) :
  PMor@{o} X PIndiscrete := @Build_PMor X PIndiscrete f (pindisc_cont X f).

Example pindisc_mor_map (X : PTop@{o}) (f : SetoidMorphism@{o o o} X S) :
  pmap (pindisc_mor X f) = f := eq_refl.

End Indiscrete.

Section IndiscreteAdjunction.

Universes o so.
Constraint o < so.

Program Definition PIndisc : Sets@{o so} ⟶ PTopCat@{o so} := {|
  fobj := fun S => PIndiscrete S;
  fmap := fun S T f => pindisc_mor T (PIndiscrete S) f
|}.
Next Obligation. intros S T f g H x; exact (H x). Qed.
Next Obligation. intros S x; reflexivity. Qed.
Next Obligation. intros S T U f g x; reflexivity. Qed.

Example PIndisc_fobj (S : Sets@{o so}) : fobj[PIndisc] S = PIndiscrete S
  := eq_refl.

Program Definition pforget_indisc_iso (X : PTopCat@{o so}) (S : Sets@{o so}) :
  @Isomorphism Sets
    {| carrier := @hom Sets@{o so} (PForget@{o so} X) S
     ; is_setoid := @homset Sets@{o so} (PForget@{o so} X) S |}
    {| carrier := @hom PTopCat@{o so} X (PIndisc S)
     ; is_setoid := @homset PTopCat@{o so} X (PIndisc S) |} := {|
  to   := {| morphism := fun k => pindisc_mor S X k |};
  from := {| morphism := fun g => pmap g |}
|}.
Next Obligation. intros X S k k' H x; exact (H x). Qed.
Next Obligation. intros X S g x; reflexivity. Qed.
Next Obligation. intros X S k x; reflexivity. Qed.

(* [PForget ⊣ PIndisc]: both transposes are the identity on underlying
   maps. *)
Definition PForget_PIndisc : PForget@{o so} ⊣ PIndisc.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PForget PIndisc pforget_indisc_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* Riehl §3.6 Proposition 2, the cocontinuity half, by Adjunction/
   Continuity.v's left adjoints preserve colimits. *)
Definition PForget_Cocontinuous : CocontinuousFunctor PForget@{o so} :=
  left_adjoint_Cocontinuous PForget_PIndisc.

End IndiscreteAdjunction.

(* The preservation statement per shape, with the shape's universes
   named. *)
Definition PForget_PreservesColimitCocone@{s o so +| o < so +}
  (J : Category@{s o o}) (K : J ⟶ PTopCat@{o so}) :
  PreservesColimitCocone K PForget@{o so} :=
  left_adjoint_PreservesColimitCocone PForget_PIndisc K.

(* The converse of the recipe: a lifted cocone that is colimiting forgets
   to a colimiting cocone, [PForget]'s image of [PFinalCocone N] having
   [N]'s apex and legs.  With [pfinal_cocone_colimiting], [N] is
   colimiting exactly when its lift is. *)
Lemma pfinal_cocone_colimiting_reflect@{o so s r x +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (H : IsColimitCocone@{x x r s o so} (PFinalCocone F N)) :
  IsColimitCocone@{x x r s o so} N.
Proof.
  exact (PForget_PreservesColimitCocone D F (PFinalCocone F N) H).
Qed.

(* Riehl's recipe in its "any colimit" form: the topology of EVERY colimit
   of spaces is the final topology on its points for its legs. *)
Lemma PTop_colimit_open_iff_final@{o so s r +| o < so +}
  {D : Category@{s o o}} {F : D ⟶ PTopCat@{o so}}
  (L : Colimit@{r s o so} F) (V : pt_carrier (colimit_apex L) → Prop) :
  POpen (colimit_apex L) V
  <-> POpen (PFinal (pt_carrier (colimit_apex L)) (obj[D]) (fun d => F d)
               (fun d => pmap (colimit_inj (colimit_is_acolimit L) d))) V.
Proof.
  split.
  - intro HV; split.
    + exact (popen_proper _ V HV).
    + intro d. exact (pcont (colimit_inj (colimit_is_acolimit L) d) V HV).
  - intro HV.
    set (N := FCocone PForget@{o so} (@limit_cone _ _ _ L)).
    pose proof (PForget_PreservesColimitCocone D F _
                  (colimit_colimitcocone L)) as HN.
    pose proof (colimitcocone_ump HN N) as U.
    destruct (colimitcocone_ump (colimit_colimitcocone L) (PFinalCocone F N))
      as [m Hm _].
    assert (Hid : ∀ y, pmap m y ≈ y).
    { intro y.
      transitivity (unique_obj U y).
      - symmetry. exact (uniqueness U (pmap m) (fun d x => Hm d x) y).
      - exact (uniqueness U setoid_morphism_id (fun d x => reflexivity _) y). }
    apply (popen_respects _ (fun y => V (pmap m y))).
    + intro y; split; intro v.
      * exact (proj1 HV _ _ (Hid y) v).
      * exact (proj1 HV _ _ (symmetry (Hid y)) v).
    + exact (pcont m V HV).
Qed.

(** ** Non-vacuity: two indiscrete two-point spaces, side by side *)

Definition PTwoIndisc@{o} : PTop@{o} := PIndiscrete bool_setoid_object@{o o}.

(* The sum, with its index universe set to the points' own, so that every
   statement below names one space. *)
Definition PTwoIndiscSum@{o u | o < u +} : PTop@{o} :=
  PSigma@{o o u} bool (fun _ => PTwoIndisc@{o}).

(* The two injections are different arrows of [PTopCat]. *)
Lemma PTwoIndiscSum_injections_differ@{o so u | o < so, o < u +} :
  psigma_inj@{o so o u} bool (fun _ => PTwoIndisc@{o}) true
    ≈[PTopCat@{o so}] psigma_inj@{o so o u} bool (fun _ => PTwoIndisc) false
  → False.
Proof. intro H. destruct (H true) as [e _]. discriminate e. Qed.

(* Each summand is open, and it is not uniform: the topology is not the
   indiscrete one. *)
Lemma PTwoIndiscSum_summand_open@{o u | o < u +} :
  POpen PTwoIndiscSum@{o u} (fun p => projT1 p = true).
Proof.
  split.
  - intros [i x] [j y] [e _] Hi; simpl in *. rewrite <- e. exact Hi.
  - intros k x y Hx. exact Hx.
Qed.

Lemma PTwoIndiscSum_not_indiscrete@{o u | o < u +} :
  (∀ U, POpen PTwoIndiscSum@{o u} U →
     ∀ p q : PTwoIndiscSum@{o u}, U p → U q) → False.
Proof.
  intro H.
  discriminate (H _ PTwoIndiscSum_summand_open
                  (existT _ true true) (existT _ false true) eq_refl).
Qed.

(* A point respecting the points' equality that is NOT open: the topology
   is not the discrete one either. *)
Lemma PTwoIndiscSum_not_discrete@{o u | o < u +} :
  (∀ p q : PTwoIndiscSum@{o u}, p ≈ q →
     projT1 p = true /\ projT2 p = true → projT1 q = true /\ projT2 q = true)
  /\ ~ POpen PTwoIndiscSum@{o u}
         (fun p => projT1 p = true /\ projT2 p = true).
Proof.
  split.
  - intros [i x] [j y] [e H] [Hi Hx]; simpl in *. destruct e. simpl in H.
    subst. split; reflexivity.
  - intros [_ Ho]. specialize (Ho true true false). simpl in Ho.
    destruct (Ho (conj eq_refl eq_refl)) as [_ H]. discriminate H.
Qed.
