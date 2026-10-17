Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.End.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(* * * Hom-函子 continuous: 同构 form consequences （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/continuous+functor

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* * * A. Awodey 7.2 -- preservation transports along natural 同构 （已译） *)

Section Transport.

Context {C D : Category}.
Context {F G : C ⟶ D}.
Context (e : F ≈ G).

Definition fun_equiv_whisker {J : Category} (K : J ⟶ C) : F ◯ K ≈ G ◯ K.
Proof using e.
  exists (fun j => `1 e (K j)).
  intros x y f; exact (`2 e _ _ (fmap[K] f)).
Defined.

Section AtDiagram.

Context {J : Category}.
Context {K : J ⟶ C}.
Context (N : Cone K).
Context (HFN : IsLimitCone (FCone F N)).

Definition transport_isalimit : IsALimit (G ◯ K) (F (vertex_obj[N])) :=
  isalimit_transport (fun_equiv_whisker K) (limitcone_isalimit HFN).

Definition transport_cone : Cone (G ◯ K) :=
  @Build_Cone J D (G ◯ K) (F (vertex_obj[N]))
    (@limit_acone _ _ _ _ transport_isalimit).

Lemma transport_coneiso_legs (x : J) :
  cone_leg (FCone G N) x ∘ to (`1 e vertex_obj[N])
    ≈ cone_leg transport_cone x.
Proof.
  simpl.
  change (cone_leg transport_cone x)
    with (to (`1 e (K x)) ∘ fmap[F] (cone_leg N x)).
  rewrite (`2 e vertex_obj[N] (K x) (cone_leg N x)).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Definition transport_coneiso : ConeIso transport_cone (FCone G N) :=
  (`1 e vertex_obj[N] ; transport_coneiso_legs).

Definition transport_islimitcone : IsLimitCone (FCone G N) :=
  limitcone_transport transport_coneiso
    (isalimit_limitcone transport_isalimit).

End AtDiagram.

Definition PreservesLimitCone_transport {J : Category} {K : J ⟶ C}
  (P : PreservesLimitCone K F) : PreservesLimitCone K G :=
  fun N HN => transport_islimitcone N (P N HN).

Definition ContinuousFunctor_transport (P : ContinuousFunctor F) :
  ContinuousFunctor G :=
  fun J K => PreservesLimitCone_transport (P J K).

End Transport.

(* 相关说明。 （已译） *)

Section RoundTrip.

Context {J C : Category}.
Context {F : J ⟶ C}.

Program Definition cone_of_nat_mor (X : C) :
  ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram X F))
    ~{Sets}~> fobj[ConePresheaf F] X :=
  {| morphism := cone_of_nat X |}.
Next Obligation. intros X α β Hαβ j; exact (Hαβ j ttt). Qed.

Program Definition nat_of_cone_mor (X : C) :
  fobj[ConePresheaf F] X
    ~{Sets}~> ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram X F)) :=
  {| morphism := nat_of_cone X |}.
Next Obligation. intros X κ κ' H j u; exact (H j). Qed.

Lemma nat_cone_nat (X : C)
  (α : Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram X F) :
  nat_of_cone X (cone_of_nat X α) ≈ α.
Proof. intros j u; destruct u; reflexivity. Qed.

Lemma cone_nat_cone (X : C) (κ : ACone X F) :
  cone_of_nat X (nat_of_cone X κ) ≈ κ.
Proof. intro j; reflexivity. Qed.

Program Definition cone_nat_iso (X : C) :
  @Isomorphism Sets
    ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram X F))
    (fobj[ConePresheaf F] X) :=
  {| to := cone_of_nat_mor X ; from := nat_of_cone_mor X |}.
Next Obligation. intros X κ; exact (cone_nat_cone X κ). Qed.
Next Obligation. intros X α; exact (nat_cone_nat X α). Qed.

Lemma cone_of_nat_natural {X X' : C} (h : X' ~{C}~> X)
  (α : Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram X F) :
  cone_of_nat X' (nat_compose (HomDiagram_precompose h F) α)
    ≈ fmap[ConePresheaf F] (h : X ~{C^op}~> X') (cone_of_nat X α).
Proof. intro j; simpl; reflexivity. Qed.

Lemma nat_of_cone_natural {X X' : C} (h : X' ~{C}~> X) (κ : ACone X F) :
  nat_of_cone X' (fmap[ConePresheaf F] (h : X ~{C^op}~> X') κ)
    ≈ nat_compose (HomDiagram_precompose h F) (nat_of_cone X κ).
Proof. intros j u; simpl; reflexivity. Qed.

(* 相关说明。 （已译） *)

Program Definition limtuple_to_cone (X : C) :
  Sets_limit_obj (HomDiagram X F) ~{Sets}~> fobj[ConePresheaf F] X :=
  {| morphism := fun p => {| vertex_map := fun j => `1 p j |} |}.
Next Obligation. intros X p j j' g; exact (`2 p j j' g). Qed.
Next Obligation. intros X p q Hpq j; exact (Hpq j). Qed.

Program Definition cone_to_limtuple (X : C) :
  fobj[ConePresheaf F] X ~{Sets}~> Sets_limit_obj (HomDiagram X F) :=
  {| morphism := fun κ =>
       (fun j => @vertex_map _ _ _ _ κ j;
        fun j j' g => @cone_coherence _ _ _ _ κ j j' g) |}.
Next Obligation. intros X κ κ' H j; exact (H j). Qed.

Program Definition limtuple_cone_iso (X : C) :
  @Isomorphism Sets (Sets_limit_obj (HomDiagram X F)) (fobj[ConePresheaf F] X) :=
  {| to := limtuple_to_cone X ; from := cone_to_limtuple X |}.
Next Obligation. intros X κ j; reflexivity. Qed.
Next Obligation. intros X p j; reflexivity. Qed.

End RoundTrip.

(* 相关说明。 （已译） *)

Section EndBridge.

Context {J C : Category}.
Context (X : C).
Context (F : J ⟶ C).

Definition homend_functor : J^op ∏ J ⟶ Sets := HomDiagram X F ◯ Snd.

Program Definition end_to_limtuple :
  Sets_End_obj homend_functor ~{Sets}~> Sets_limit_obj (HomDiagram X F) :=
  {| morphism := fun s => (fun j => `1 s j ; _) |}.
Next Obligation.
  intros s j j' g; simpl.
  rewrite (`2 s j j' g); simpl.
  now rewrite fmap_id, id_left.
Qed.
Next Obligation. intros s t Hst j; exact (Hst j). Qed.

Program Definition limtuple_to_end :
  Sets_limit_obj (HomDiagram X F) ~{Sets}~> Sets_End_obj homend_functor :=
  {| morphism := fun p => (fun j => `1 p j ; _) |}.
Next Obligation.
  intros p j j' g; simpl.
  rewrite fmap_id, id_left.
  exact (`2 p j j' g).
Qed.
Next Obligation. intros p q Hpq j; exact (Hpq j). Qed.

Program Definition end_limtuple_iso :
  Sets_End_obj homend_functor ≅[Sets] Sets_limit_obj (HomDiagram X F) :=
  {| to := end_to_limtuple ; from := limtuple_to_end |}.
Next Obligation. intros p j; reflexivity. Qed.
Next Obligation. intros s j; reflexivity. Qed.

(* 相关说明。 （已译） *)
Program Definition end_cone : Cone (HomDiagram X F) :=
  {| vertex_obj := Sets_End_obj homend_functor
   ; coneFrom := {| vertex_map := fun j => end_projection homend_functor j |} |}.
Next Obligation.
  intros j j' g s; simpl.
  rewrite (`2 s j j' g); simpl.
  now rewrite fmap_id, id_left.
Qed.

Definition end_coneiso : ConeIso (Sets_limit_cone (HomDiagram X F)) end_cone.
Proof.
  exists (iso_sym end_limtuple_iso).
  intros j p; reflexivity.
Defined.

(* 相关说明。 （已译） *)
Definition end_IsLimitCone : IsLimitCone end_cone :=
  limitcone_transport end_coneiso
    (limit_limitcone (Sets_Limit (HomDiagram X F))).

Definition end_Limit : Limit (HomDiagram X F) :=
  limitcone_limit end_cone end_IsLimitCone.

End EndBridge.

(* 相关说明。 （已译） *)

Section Remark2.

Context {J C : Category}.
Context {F : J ⟶ C}.
Context (L : Limit F).

Definition homlim_cone (c : C) : Cone (HomFrom c ◯ F) :=
  @limit_cone _ _ _ (Sets_Limit (HomFrom c ◯ F)).

Definition homlim_islimit (c : C) : IsLimitCone (homlim_cone c) :=
  limit_limitcone (Sets_Limit (HomFrom c ◯ F)).

Definition homimg_islimit (c : C) :
  IsLimitCone (FCone (HomFrom c) (@limit_cone _ _ _ L)) :=
  hom_PreservesLimitCone c F (@limit_cone _ _ _ L) (limit_limitcone L).

Definition remark2_coneiso (c : C) :
  ConeIso (homlim_cone c) (FCone (HomFrom c) (@limit_cone _ _ _ L)) :=
  limitcone_iso (homlim_islimit c) (homimg_islimit c).

Definition remark2_iso (c : C) :
  @Isomorphism Sets (Sets_limit_obj (HomFrom c ◯ F))
    {| carrier := c ~{C}~> vertex_obj[@limit_cone _ _ _ L]
     ; is_setoid := @homset C c (vertex_obj[@limit_cone _ _ _ L]) |} :=
  `1 (remark2_coneiso c).

Lemma remark2_iso_legs (c : C) (p : Sets_limit_obj (HomFrom c ◯ F)) (j : J) :
  cone_leg (@limit_cone _ _ _ L) j ∘ to (remark2_iso c) p ≈ `1 p j.
Proof. exact (`2 (remark2_coneiso c) j p). Qed.

Lemma remark2_iso_from (c : C) (u : c ~{C}~> vertex_obj[@limit_cone _ _ _ L])
  (j : J) :
  `1 (from (remark2_iso c) u) j ≈ cone_leg (@limit_cone _ _ _ L) j ∘ u.
Proof. exact (coneiso_from (remark2_coneiso c) j u). Qed.

Program Definition homlim_reindex {c c' : C} (h : c' ~{C}~> c) :
  Sets_limit_obj (HomFrom c ◯ F) ~{Sets}~> Sets_limit_obj (HomFrom c' ◯ F) :=
  {| morphism := fun p => (fun j => `1 p j ∘ h; _) |}.
Next Obligation.
  intros c c' h p j j' g; simpl.
  rewrite comp_assoc.
  now rewrite (`2 p j j' g).
Qed.
Next Obligation.
  intros c c' h p q Hpq j; simpl; now rewrite (Hpq j).
Qed.

Program Definition remark2_reindexed_cone {c c' : C} (h : c' ~{C}~> c)
  (p : Sets_limit_obj (HomFrom c ◯ F)) : Cone F :=
  {| vertex_obj := c'
   ; coneFrom := {| vertex_map := fun j => `1 p j ∘ h |} |}.
Next Obligation.
  intros c c' h p j j' g; simpl.
  rewrite comp_assoc.
  now rewrite (`2 p j j' g).
Qed.

Theorem remark2_natural {c c' : C} (h : c' ~{C}~> c)
  (p : Sets_limit_obj (HomFrom c ◯ F)) :
  to (remark2_iso c') (homlim_reindex h p) ≈ to (remark2_iso c) p ∘ h.
Proof.
  apply (limit_med_eq (limit_is_alimit L) (remark2_reindexed_cone h p)).
  - intro j; simpl.
    exact (remark2_iso_legs c' (homlim_reindex h p) j).
  - intro j; simpl.
    rewrite comp_assoc.
    now rewrite (remark2_iso_legs c p j).
Qed.

(* Riehl 3.5.3 in her own direction: the CANONICAL comparison map
   C(c, lim F) --> lim C(c, F-) is invertible.  This performs the
   composition Functor/Hom/Limit.v's header records as not performed. *)
Definition remark2_comparison (c : C) :
  fobj[HomFrom c] (vertex_obj[@limit_cone _ _ _ L])
    ~{Sets}~> Sets_limit_obj (HomFrom c ◯ F) :=
  cone_comparison (HomFrom c) (@limit_cone _ _ _ L) (homlim_islimit c).

Definition remark2_comparison_iso (c : C) :
  IsIsomorphism (remark2_comparison c) :=
  comparison_iso_of_PreservesLimitCone (HomFrom c)
    (hom_PreservesLimitCone c F) (homlim_islimit c)
    (@limit_cone _ _ _ L) (limit_limitcone L).

End Remark2.

(* 相关说明。 （已译） *)

Section Remark3.

Context {J C : Category}.
Context {F : J ⟶ C}.
Context (L : Colimit F).

(* Pure instantiation Remark 2 at opposite 范畴: [Colimit F] IS
 [Limit (F^op)] [HomTo c] IS [HomFrom c] [C^op]. （已译） *)
Definition remark3_iso (c : C) :
  @Isomorphism Sets (Sets_limit_obj (HomTo c ◯ F^op))
    {| carrier := vertex_obj[@limit_cone _ _ _ L] ~{C}~> c
     ; is_setoid := @homset (C^op) c (vertex_obj[@limit_cone _ _ _ L]) |} :=
  @remark2_iso (J^op) (C^op) (F^op) L c.

Theorem remark3_natural {c c' : C} (h : c ~{C}~> c')
  (p : Sets_limit_obj (HomTo c ◯ F^op)) :
  to (remark3_iso c') (@homlim_reindex (J^op) (C^op) (F^op) c c' h p)
    ≈ to (remark3_iso c) p ∘[C^op] h.
Proof. exact (@remark2_natural (J^op) (C^op) (F^op) L c c' h p). Qed.

End Remark3.

(* * * F. The product coproduct instances, isomorphisms of
 Sets-对象 rather than family-level universal properties （已译） *)

Section ProductInstance.

Context {C : Category}.
Context (c : C).
Context {A : Type}.
Context {f : A → C}.
Context {p : C}.
Context {proj : ∀ a : A, p ~{C}~> f a}.
Context (H : IsIndexedProduct f p proj).

Definition hom_iprod_iso :
  fobj[HomFrom c] p ≅[Sets] Sets_iprod_obj (fun a => fobj[HomFrom c] (f a)) :=
  iprod_unique_iso (fun a => fobj[HomFrom c] (f a)) _ _ _ _
    (hom_IsIndexedProduct c H)
    (Sets_IsIndexedProduct (fun a => fobj[HomFrom c] (f a))).

Lemma hom_iprod_iso_to (u : c ~{C}~> p) (a : A) :
  to hom_iprod_iso u a ≈ proj a ∘ u.
Proof.
  exact (iprod_compare_commutes (fun a => fobj[HomFrom c] (f a))
           (fobj[HomFrom c] p)
           (Sets_iprod_obj (fun a => fobj[HomFrom c] (f a)))
           (fun a => fmap[HomFrom c] (proj a))
           (Sets_iprod_proj (fun a => fobj[HomFrom c] (f a)))
           (Sets_IsIndexedProduct (fun a => fobj[HomFrom c] (f a))) a u).
Qed.

End ProductInstance.

Section CoproductInstance.

Context {C : Category}.
Context (c : C).
Context {A : Type}.
Context {g : A → C}.
Context {q : C}.
Context {inj : ∀ a : A, g a ~{C}~> q}.
Context (H : IsIndexedCoproduct g q inj).

Definition cohom_icoprod_iso :
  fobj[HomTo c] q ≅[Sets] Sets_iprod_obj (fun a => fobj[HomTo c] (g a)) :=
  iprod_unique_iso (fun a => fobj[HomTo c] (g a)) _ _ _ _
    (cohom_IsIndexedProduct c H)
    (Sets_IsIndexedProduct (fun a => fobj[HomTo c] (g a))).

Lemma cohom_icoprod_iso_to (u : q ~{C}~> c) (a : A) :
  to cohom_icoprod_iso u a ≈ u ∘ inj a.
Proof.
  exact (iprod_compare_commutes (fun a => fobj[HomTo c] (g a))
           (fobj[HomTo c] q)
           (Sets_iprod_obj (fun a => fobj[HomTo c] (g a)))
           (fun a => fmap[HomTo c] (inj a))
           (Sets_iprod_proj (fun a => fobj[HomTo c] (g a)))
           (Sets_IsIndexedProduct (fun a => fobj[HomTo c] (g a))) a u).
Qed.

End CoproductInstance.


(* Naturality in c of the two product instances, which is what makes them
   natural isomorphisms of Sets-objects rather than pointwise bijections. *)

Lemma hom_iprod_iso_natural {C : Category} {A : Type} {f : A → C} {p : C}
  {proj : ∀ a : A, p ~{C}~> f a} (H : IsIndexedProduct f p proj)
  {c c' : C} (h : c' ~{C}~> c) (u : c ~{C}~> p) (a : A) :
  to (hom_iprod_iso c' H) (u ∘ h) a ≈ to (hom_iprod_iso c H) u a ∘ h.
Proof.
  rewrite (hom_iprod_iso_to c' H (u ∘ h) a).
  rewrite (hom_iprod_iso_to c H u a).
  now rewrite comp_assoc.
Qed.

Lemma cohom_icoprod_iso_natural {C : Category} {A : Type} {g : A → C} {q : C}
  {inj : ∀ a : A, g a ~{C}~> q} (H : IsIndexedCoproduct g q inj)
  {c c' : C} (h : c ~{C}~> c') (u : q ~{C}~> c) (a : A) :
  to (cohom_icoprod_iso c' H) (h ∘ u) a ≈ h ∘ to (cohom_icoprod_iso c H) u a.
Proof.
  rewrite (cohom_icoprod_iso_to c' H (h ∘ u) a).
  rewrite (cohom_icoprod_iso_to c H u a).
  now rewrite comp_assoc.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Continuous 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hom_preserves_limits {C : Category} (c : C) :
  ContinuousFunctor (@HomFrom C c) := hom_ContinuousFunctor c.

Definition cohom_carries_colimits_to_limits {C : Category} (c : C)
  {J : Category} {K : J ⟶ C} (N : Cocone K) (HN : IsColimitCocone N) :
  IsLimitCone (FCone (HomTo c) N) := cohom_colimit_to_limit c N HN.

(* Awodey §7.2's remark as stated: a functor naturally isomorphic to a
   representable preserves limits — one application of section A to #331. *)
Definition representable_iso_ContinuousFunctor {C : Category} (c : C)
  {G : C ⟶ Sets} (e : @HomFrom C c ≈ G) : ContinuousFunctor G :=
  ContinuousFunctor_transport e (hom_ContinuousFunctor c).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HomFrom_at@{o h s +} {C : Category@{o h h}} (c : C) :
  C ⟶ Sets@{h s} := @HomFrom C c.

Definition hom_continuous_at@{o h s +} {C : Category@{o h h}} (c : C) :
  ContinuousFunctor (@HomFrom_at C c : C ⟶ Sets@{h s}) :=
  hom_ContinuousFunctor c.
