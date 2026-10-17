(** * Limits and colimits as adjoints of the diagonal functor *)

(*
   nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Kan.Extension.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.

Generalizable All Variables.

(** * Shape-indexed limit and colimit hypotheses *)

Definition HasLimitsOfShape (J C : Category) : Type := ∀ F : J ⟶ C, Limit F.

Definition HasColimitsOfShape (J C : Category) : Type :=
  ∀ F : J ⟶ C, Colimit F.

Definition Complete_HasLimitsOfShape {C : Category} (H : @Complete C)
  (J : Category) : HasLimitsOfShape J C := H J.

Definition Cocomplete_HasColimitsOfShape {C : Category} (H : @Cocomplete C)
  (J : Category) : HasColimitsOfShape J C := H J.

(** * The limit functor and the adjunction Δ ⊣ lim *)

Section LimitAdjunction.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).

Definition lim_obj (F : J ⟶ C) : C := vertex_obj[@limit_cone J C F (L F)].

Definition lim_alimit (F : J ⟶ C) : IsALimit F (lim_obj F) :=
  limit_is_alimit (L F).

Definition lim_leg (F : J ⟶ C) (j : J) : lim_obj F ~{C}~> F j :=
  limit_leg (lim_alimit F) j.

Lemma lim_leg_coherence (F : J ⟶ C) {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ lim_leg F x ≈ lim_leg F y.
Proof. exact (limit_leg_coherence (lim_alimit F) f). Qed.

Definition lim_med {F : J ⟶ C} (N : Cone F) :
  vertex_obj[N] ~{C}~> lim_obj F := limit_med (lim_alimit F) N.

Lemma lim_med_commutes {F : J ⟶ C} (N : Cone F) (j : J) :
  lim_leg F j ∘ lim_med N ≈ cone_leg N j.
Proof. exact (limit_med_commutes (lim_alimit F) N j). Qed.

Lemma lim_med_unique {F : J ⟶ C} (N : Cone F)
  (u : vertex_obj[N] ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ cone_leg N j) → lim_med N ≈ u.
Proof. exact (limit_med_unique (lim_alimit F) N u). Qed.

Lemma lim_med_eq {F : J ⟶ C} (N : Cone F)
  (u v : vertex_obj[N] ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ cone_leg N j) →
  (∀ j : J, lim_leg F j ∘ v ≈ cone_leg N j) → u ≈ v.
Proof. exact (limit_med_eq (lim_alimit F) N u v). Qed.

(** ** The action on natural transformations *)

Program Definition Lim_cone {F G : J ⟶ C} (b : F ⟹ G) : Cone G := {|
  vertex_obj := lim_obj F;
  coneFrom := {| vertex_map := fun j => transform[b] j ∘ lim_leg F j |}
|}.
Next Obligation.
  rewrite comp_assoc, naturality, <- comp_assoc, lim_leg_coherence.
  reflexivity.
Qed.

Definition Lim_map {F G : J ⟶ C} (b : F ⟹ G) : lim_obj F ~{C}~> lim_obj G :=
  lim_med (Lim_cone b).

Lemma Lim_map_commutes {F G : J ⟶ C} (b : F ⟹ G) (j : J) :
  lim_leg G j ∘ Lim_map b ≈ transform[b] j ∘ lim_leg F j.
Proof. exact (lim_med_commutes (Lim_cone b) j). Qed.

Lemma Lim_map_unique {F G : J ⟶ C} (b : F ⟹ G)
  (u : lim_obj F ~{C}~> lim_obj G) :
  (∀ j : J, lim_leg G j ∘ u ≈ transform[b] j ∘ lim_leg F j) → Lim_map b ≈ u.
Proof. exact (lim_med_unique (Lim_cone b) u). Qed.

Program Definition LimitFunctor : [J, C] ⟶ C := {|
  fobj := lim_obj;
  fmap := fun _ _ b => Lim_map b
|}.
Next Obligation.
  proper.
  symmetry.
  apply Lim_map_unique; intro j.
  rewrite Lim_map_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply Lim_map_unique; intro j.
  simpl.
  now rewrite id_right, fmap_id, id_left.
Qed.
Next Obligation.
  apply Lim_map_unique; intro j.
  rewrite comp_assoc, Lim_map_commutes.
  rewrite <- comp_assoc, Lim_map_commutes.
  now rewrite comp_assoc.
Qed.

(** ** The hom-set bijection Δ(x) ⟹ F  ≅  x ~> lim F *)

Program Definition lim_precone {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) : ACone x F := {|
  vertex_map := fun j => lim_leg F j ∘ h
|}.
Next Obligation. now rewrite comp_assoc, lim_leg_coherence. Qed.

Definition lim_transpose_from {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) : Δ[J](x) ⟹ F :=
  snd (Cone_Natural_Transform F x) (lim_precone h).

Definition lim_transpose_cone {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) : Cone F :=
  {| vertex_obj := x; coneFrom := fst (Cone_Natural_Transform F x) t |}.

Definition lim_transpose_to {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) : x ~{C}~> lim_obj F := lim_med (lim_transpose_cone t).

Lemma lim_transpose_to_commutes {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  lim_leg F j ∘ lim_transpose_to t ≈ transform[t] j.
Proof. exact (lim_med_commutes (lim_transpose_cone t) j). Qed.

Lemma lim_transpose_to_unique {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (u : x ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ transform[t] j) → lim_transpose_to t ≈ u.
Proof. exact (lim_med_unique (lim_transpose_cone t) u). Qed.

Lemma lim_transpose_from_component {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) (j : J) :
  transform[lim_transpose_from h] j = lim_leg F j ∘ h.
Proof. reflexivity. Qed.

(** The donor's bijection is definitional on components, in both
    directions; the whole construction rests on these two. *)

Example cone_natural_transform_to_component {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  @vertex_map J C x F (fst (Cone_Natural_Transform F x) t) j
    = transform[t] j := eq_refl.

Example cone_natural_transform_from_component {F : J ⟶ C} {x : C}
  (a : ACone x F) (j : J) :
  transform[snd (Cone_Natural_Transform F x) a] j
    = @vertex_map J C x F a j := eq_refl.

Program Definition lim_adj_iso (x : C) (F : J ⟶ C) :
  @Isomorphism Sets
    {| carrier   := @hom ([J, C]) (Δ[J](x)) F
     ; is_setoid := @homset ([J, C]) (Δ[J](x)) F |}
    {| carrier   := @hom C x (lim_obj F)
     ; is_setoid := @homset C x (lim_obj F) |} := {|
  to   := {| morphism := fun t => lim_transpose_to t |};
  from := {| morphism := fun h => lim_transpose_from h |}
|}.
Next Obligation.
  proper.
  apply lim_transpose_to_unique; intro j.
  rewrite lim_transpose_to_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  now rewrite lim_transpose_from_component.
Qed.
Next Obligation.
  apply lim_transpose_to_commutes.
Qed.

Program Definition Diagonal_Limit_Adjunction : @Diagonal C J ⊣ LimitFunctor :=
  {| adj := lim_adj_iso |}.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  rewrite comp_assoc, lim_transpose_to_commutes.
  reflexivity.
Qed.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  rewrite comp_assoc, Lim_map_commutes.
  rewrite <- comp_assoc, lim_transpose_to_commutes.
  reflexivity.
Qed.
Next Obligation.
  rewrite !comp_assoc, Lim_map_commutes.
  reflexivity.
Qed.

(** ** Riehl §4.6 exercise ii: the counit is the limiting cone *)

Definition lim_counit (F : J ⟶ C) : Δ[J](lim_obj F) ⟹ F :=
  @counit ([J, C]) C (@Diagonal C J) LimitFunctor
          Diagonal_Limit_Adjunction F.

Example lim_counit_component_strict (F : J ⟶ C) (j : J) :
  transform[lim_counit F] j = lim_leg F j ∘ id := eq_refl.

Lemma lim_counit_is_limit_leg (F : J ⟶ C) (j : J) :
  transform[lim_counit F] j ≈ lim_leg F j.
Proof. rewrite lim_counit_component_strict; now rewrite id_right. Qed.

(** ** Readbacks against the donor vocabulary *)

Example lim_obj_is_limit_apex (F : J ⟶ C) :
  fobj[LimitFunctor] F = vertex_obj[@limit_cone J C F (L F)] := eq_refl.

Example lim_leg_is_limit_leg (F : J ⟶ C) (j : J) :
  lim_leg F j = limit_leg (lim_alimit F) j := eq_refl.

Example lim_med_is_limit_med {F : J ⟶ C} (N : Cone F) :
  lim_med N = limit_med (lim_alimit F) N := eq_refl.

Example Lim_map_is_fmap {F G : J ⟶ C} (b : F ⟹ G) :
  fmap[LimitFunctor] b = Lim_map b := eq_refl.

Example lim_transpose_to_is_adj {F : J ⟶ C} {x : C} (t : Δ[J](x) ⟹ F) :
  to (@adj ([J, C]) C (@Diagonal C J) LimitFunctor
           Diagonal_Limit_Adjunction x F) t = lim_transpose_to t := eq_refl.

Example lim_transpose_from_is_adj {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) :
  from (@adj ([J, C]) C (@Diagonal C J) LimitFunctor
             Diagonal_Limit_Adjunction x F) h = lim_transpose_from h
  := eq_refl.

End LimitAdjunction.

(** * The colimit functor and the adjunction colim ⊣ Δ *)

Section ColimitAdjunction.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).

Definition colim_obj (F : J ⟶ C) : C := colimit_apex (L F).

Definition colim_acolimit (F : J ⟶ C) : IsAColimit F (colim_obj F) :=
  colimit_is_acolimit (L F).

Definition colim_inj (F : J ⟶ C) (j : J) : F j ~{C}~> colim_obj F :=
  colimit_inj (colim_acolimit F) j.

Lemma colim_inj_coherence (F : J ⟶ C) {x y : J} (f : x ~{J}~> y) :
  colim_inj F y ∘ fmap[F] f ≈ colim_inj F x.
Proof. exact (colimit_inj_coherence (colim_acolimit F) f). Qed.

Definition colim_med {F : J ⟶ C} (N : Cocone F) :
  colim_obj F ~{C}~> vertex_obj[N] := colimit_med (colim_acolimit F) N.

Lemma colim_med_commutes {F : J ⟶ C} (N : Cocone F) (j : J) :
  colim_med N ∘ colim_inj F j ≈ cocone_inj N j.
Proof. exact (colimit_med_commutes (colim_acolimit F) N j). Qed.

Lemma colim_med_unique {F : J ⟶ C} (N : Cocone F)
  (u : colim_obj F ~{C}~> vertex_obj[N]) :
  (∀ j : J, u ∘ colim_inj F j ≈ cocone_inj N j) → colim_med N ≈ u.
Proof. exact (colimit_med_unique (colim_acolimit F) N u). Qed.

Lemma colim_med_eq {F : J ⟶ C} (N : Cocone F)
  (u v : colim_obj F ~{C}~> vertex_obj[N]) :
  (∀ j : J, u ∘ colim_inj F j ≈ cocone_inj N j) →
  (∀ j : J, v ∘ colim_inj F j ≈ cocone_inj N j) → u ≈ v.
Proof. exact (colimit_med_eq (colim_acolimit F) N u v). Qed.

(** ** Building cocones covariantly *)

Program Definition Cocone_of {F : J ⟶ C} (c : C)
  (i : ∀ j : J, F j ~{C}~> c)
  (Hi : ∀ (x y : J) (f : x ~{J}~> y), i y ∘ fmap[F] f ≈ i x) : Cocone F := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := i |}
|}.

Example cocone_of_inj {F : J ⟶ C} (c : C) i Hi (j : J) :
  cocone_inj (@Cocone_of F c i Hi) j = i j := eq_refl.

(** ** The dual of [Cone_Natural_Transform] *)

Program Definition cocone_of_transform {F : J ⟶ C} {N : C}
  (t : F ⟹ Δ[J](N)) : Cocone F :=
  Cocone_of N (fun j => transform[t] j) _.
Next Obligation.
  pose proof (@naturality_sym J C F (Δ[J](N)) t x y f) as HN.
  rewrite HN.
  apply id_left.
Qed.

Definition cocone_apex {F : J ⟶ C} (N : Cocone F) : C :=
  @vertex_obj (J^op) (C^op) (F^op) N.

Program Definition transform_of_cocone {F : J ⟶ C} (N : Cocone F) :
  F ⟹ Δ[J](cocone_apex N) := {|
  transform := fun j => cocone_inj N j
|}.
Next Obligation.
  rewrite (cocone_inj_coherence N f); apply id_left.
Qed.
Next Obligation.
  rewrite (cocone_inj_coherence N f); symmetry; apply id_left.
Qed.

Example cocone_of_transform_inj {F : J ⟶ C} {N : C}
  (t : F ⟹ Δ[J](N)) (j : J) :
  cocone_inj (cocone_of_transform t) j = transform[t] j := eq_refl.

Example transform_of_cocone_component {F : J ⟶ C} (N : Cocone F) (j : J) :
  transform[transform_of_cocone N] j = cocone_inj N j := eq_refl.

Lemma Cocone_Natural_Transform (F : J ⟶ C) (N : C) :
  (F ⟹ Δ[J](N)) ↔ @ACone (J^op) (C^op) N (F^op).
Proof.
  split; intro t.
  - exact (@coneFrom (J^op) (C^op) (F^op) (cocone_of_transform t)).
  - exact (transform_of_cocone (@Build_Cone (J^op) (C^op) (F^op) N t)).
Defined.

(** ** The action on natural transformations *)

Program Definition Colim_cocone {F G : J ⟶ C} (b : F ⟹ G) : Cocone F :=
  Cocone_of (colim_obj G) (fun j => colim_inj G j ∘ transform[b] j) _.
Next Obligation.
  pose proof (@naturality J C F G b x y f) as HN.
  rewrite <- comp_assoc, <- HN.
  now rewrite comp_assoc, colim_inj_coherence.
Qed.

Definition Colim_map {F G : J ⟶ C} (b : F ⟹ G) :
  colim_obj F ~{C}~> colim_obj G := colim_med (Colim_cocone b).

Lemma Colim_map_commutes {F G : J ⟶ C} (b : F ⟹ G) (j : J) :
  Colim_map b ∘ colim_inj F j ≈ colim_inj G j ∘ transform[b] j.
Proof. exact (colim_med_commutes (Colim_cocone b) j). Qed.

Lemma Colim_map_unique {F G : J ⟶ C} (b : F ⟹ G)
  (u : colim_obj F ~{C}~> colim_obj G) :
  (∀ j : J, u ∘ colim_inj F j ≈ colim_inj G j ∘ transform[b] j) →
  Colim_map b ≈ u.
Proof. exact (colim_med_unique (Colim_cocone b) u). Qed.

Program Definition ColimitFunctor : [J, C] ⟶ C := {|
  fobj := colim_obj;
  fmap := fun _ _ b => Colim_map b
|}.
Next Obligation.
  proper.
  symmetry.
  apply Colim_map_unique; intro j.
  rewrite Colim_map_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply Colim_map_unique; intro j.
  simpl.
  now rewrite id_left, fmap_id, id_right.
Qed.
Next Obligation.
  apply Colim_map_unique; intro j.
  rewrite <- comp_assoc, Colim_map_commutes.
  rewrite comp_assoc, Colim_map_commutes.
  now rewrite <- comp_assoc.
Qed.

(** ** The hom-set bijection colim F ~> y  ≅  F ⟹ Δ(y) *)

Program Definition colim_transpose_to {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) : F ⟹ Δ[J](y) := {|
  transform := fun j => u ∘ colim_inj F j
|}.
Next Obligation.
  now rewrite <- comp_assoc, (colim_inj_coherence F f), id_left.
Qed.
Next Obligation.
  now rewrite <- comp_assoc, (colim_inj_coherence F f), id_left.
Qed.

Definition colim_transpose_from {F : J ⟶ C} {y : C} (t : F ⟹ Δ[J](y)) :
  colim_obj F ~{C}~> y := colim_med (cocone_of_transform t).

Lemma colim_transpose_from_commutes {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (j : J) :
  colim_transpose_from t ∘ colim_inj F j ≈ transform[t] j.
Proof. exact (colim_med_commutes (cocone_of_transform t) j). Qed.

Lemma colim_transpose_from_unique {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (u : colim_obj F ~{C}~> y) :
  (∀ j : J, u ∘ colim_inj F j ≈ transform[t] j) → colim_transpose_from t ≈ u.
Proof. exact (colim_med_unique (cocone_of_transform t) u). Qed.

Lemma colim_transpose_to_component {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) (j : J) :
  transform[colim_transpose_to u] j = u ∘ colim_inj F j.
Proof. reflexivity. Qed.

Program Definition colim_adj_iso (F : J ⟶ C) (y : C) :
  @Isomorphism Sets
    {| carrier   := @hom C (colim_obj F) y
     ; is_setoid := @homset C (colim_obj F) y |}
    {| carrier   := @hom ([J, C]) F (Δ[J](y))
     ; is_setoid := @homset ([J, C]) F (Δ[J](y)) |} := {|
  to   := {| morphism := fun u => colim_transpose_to u |};
  from := {| morphism := fun t => colim_transpose_from t |}
|}.
Next Obligation.
  proper.
  apply colim_transpose_from_unique; intro j.
  rewrite colim_transpose_from_commutes.
  now rewrite (X j).
Qed.
Next Obligation. apply colim_transpose_from_commutes. Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  now rewrite colim_transpose_to_component.
Qed.

Program Definition Colimit_Diagonal_Adjunction :
  ColimitFunctor ⊣ @Diagonal C J := {| adj := colim_adj_iso |}.
Next Obligation.
  rewrite <- comp_assoc, Colim_map_commutes.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  rewrite <- comp_assoc, Colim_map_commutes.
  now rewrite comp_assoc, colim_transpose_from_commutes.
Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  now rewrite <- comp_assoc, colim_transpose_from_commutes.
Qed.

(** ** Riehl §4.6 exercise ii: the unit is the colimiting cocone *)

Definition colim_unit (F : J ⟶ C) : F ⟹ Δ[J](colim_obj F) :=
  @unit C ([J, C]) ColimitFunctor (@Diagonal C J)
        Colimit_Diagonal_Adjunction F.

Example colim_unit_component_strict (F : J ⟶ C) (j : J) :
  transform[colim_unit F] j = id ∘ colim_inj F j := eq_refl.

Lemma colim_unit_is_colimit_inj (F : J ⟶ C) (j : J) :
  transform[colim_unit F] j ≈ colim_inj F j.
Proof. rewrite colim_unit_component_strict; now rewrite id_left. Qed.

(** ** Readbacks against the donor vocabulary *)

Example colim_obj_is_colimit_apex (F : J ⟶ C) :
  fobj[ColimitFunctor] F = colimit_apex (L F) := eq_refl.

Example colim_inj_is_colimit_inj (F : J ⟶ C) (j : J) :
  colim_inj F j = colimit_inj (colim_acolimit F) j := eq_refl.

Example colim_med_is_colimit_med {F : J ⟶ C} (N : Cocone F) :
  colim_med N = colimit_med (colim_acolimit F) N := eq_refl.

Example Colim_map_is_fmap {F G : J ⟶ C} (b : F ⟹ G) :
  fmap[ColimitFunctor] b = Colim_map b := eq_refl.

Example colim_transpose_to_is_adj {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) :
  to (@adj C ([J, C]) ColimitFunctor (@Diagonal C J)
           Colimit_Diagonal_Adjunction F y) u = colim_transpose_to u
  := eq_refl.

Example colim_transpose_from_is_adj {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) :
  from (@adj C ([J, C]) ColimitFunctor (@Diagonal C J)
             Colimit_Diagonal_Adjunction F y) t = colim_transpose_from t
  := eq_refl.

End ColimitAdjunction.

(** * Riehl §4.6 Proposition 4.6.1, the converse directions *)

Section RightAdjointGivesLimits.

Context {J C : Category}.
Context {R : [J, C] ⟶ C}.
Context (A : @Diagonal C J ⊣ R).

Definition radj_counit (F : J ⟶ C) : Δ[J](R F) ⟹ F :=
  @counit ([J, C]) C (@Diagonal C J) R A F.

Definition radj_transpose {x : C} {F : J ⟶ C} (t : Δ[J](x) ⟹ F) :
  x ~{C}~> R F := to (@adj ([J, C]) C (@Diagonal C J) R A x F) t.

Lemma radj_transpose_commutes {x : C} {F : J ⟶ C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  transform[radj_counit F] j ∘ radj_transpose t ≈ transform[t] j.
Proof.
  pose proof (snd (@adj_univ_impl ([J, C]) C (@Diagonal C J) R A x F t
                     (radj_transpose t)) (reflexivity _)) as HU.
  symmetry; exact (HU j).
Qed.

Lemma radj_transpose_unique {x : C} {F : J ⟶ C}
  (t : Δ[J](x) ⟹ F) (v : x ~{C}~> R F) :
  (∀ j : J, transform[radj_counit F] j ∘ v ≈ transform[t] j) →
  radj_transpose t ≈ v.
Proof.
  intro Hv.
  apply (fst (@adj_univ_impl ([J, C]) C (@Diagonal C J) R A x F t v)).
  intro j; symmetry; exact (Hv j).
Qed.

Program Definition radj_cone (F : J ⟶ C) : Cone F := {|
  vertex_obj := R F;
  coneFrom := fst (Cone_Natural_Transform F (R F)) (radj_counit F)
|}.

Program Definition radj_Limit (F : J ⟶ C) : Limit F := {|
  limit_cone := radj_cone F
|}.
Next Obligation.
  unshelve econstructor.
  - exact (radj_transpose
             (snd (Cone_Natural_Transform F (vertex_obj[N]))
                  (@coneFrom J C F N))).
  - intro j; apply radj_transpose_commutes.
  - intros v Hv; apply radj_transpose_unique; exact Hv.
Qed.

Definition Diagonal_right_adjoint_HasLimits : HasLimitsOfShape J C :=
  radj_Limit.

End RightAdjointGivesLimits.

Section LeftAdjointGivesColimits.

Context {J C : Category}.
Context {K : [J, C] ⟶ C}.
Context (A : K ⊣ @Diagonal C J).

Definition ladj_unit (F : J ⟶ C) : F ⟹ Δ[J](K F) :=
  @unit C ([J, C]) K (@Diagonal C J) A F.

Definition ladj_transpose {F : J ⟶ C} {y : C} (t : F ⟹ Δ[J](y)) :
  K F ~{C}~> y := from (@adj C ([J, C]) K (@Diagonal C J) A F y) t.

Lemma ladj_transpose_commutes {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (j : J) :
  ladj_transpose t ∘ transform[ladj_unit F] j ≈ transform[t] j.
Proof.
  pose proof (@to_adj_unit C ([J, C]) K (@Diagonal C J) A F y
                (ladj_transpose t)) as H1.
  pose proof (@from_adj_comp_law C ([J, C]) K (@Diagonal C J) A F y t) as H2.
  rewrite <- (H1 j); exact (H2 j).
Qed.

Lemma ladj_transpose_unique {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (v : K F ~{C}~> y) :
  (∀ j : J, v ∘ transform[ladj_unit F] j ≈ transform[t] j) →
  ladj_transpose t ≈ v.
Proof.
  intro Hv.
  pose proof (@to_adj_unit C ([J, C]) K (@Diagonal C J) A F y v) as H1.
  assert (Ht : to (@adj C ([J, C]) K (@Diagonal C J) A F y) v ≈ t).
  { intro j; rewrite (H1 j); exact (Hv j). }
  transitivity (from (@adj C ([J, C]) K (@Diagonal C J) A F y)
                     (to (@adj C ([J, C]) K (@Diagonal C J) A F y) v)).
  - apply from_adj_respects; symmetry; exact Ht.
  - apply to_adj_comp_law.
Qed.

Program Definition ladj_Colimit (F : J ⟶ C) : Colimit F := {|
  limit_cone := cocone_of_transform (ladj_unit F)
|}.
Next Obligation.
  unshelve econstructor.
  - exact (ladj_transpose (transform_of_cocone N)).
  - intro j; apply ladj_transpose_commutes.
  - intros v Hv; apply ladj_transpose_unique; exact Hv.
Qed.

Definition Diagonal_left_adjoint_HasColimits : HasColimitsOfShape J C :=
  ladj_Colimit.

End LeftAdjointGivesColimits.

Theorem limits_iff_diagonal_right_adjoint (J C : Category) :
  HasLimitsOfShape J C ↔ { R : [J, C] ⟶ C & @Diagonal C J ⊣ R }.
Proof.
  split.
  - intro L; exists (LimitFunctor L); exact (Diagonal_Limit_Adjunction L).
  - intros [R A]; exact (Diagonal_right_adjoint_HasLimits A).
Defined.

Theorem colimits_iff_diagonal_left_adjoint (J C : Category) :
  HasColimitsOfShape J C ↔ { K : [J, C] ⟶ C & K ⊣ @Diagonal C J }.
Proof.
  split.
  - intro L; exists (ColimitFunctor L); exact (Colimit_Diagonal_Adjunction L).
  - intros [K A]; exact (Diagonal_left_adjoint_HasColimits A).
Defined.

(** * Awodey §9.3 / Riehl §4.6 exercise i: the degenerate rows *)

Lemma one_arrow_eq@{u} (a b : poly_unit@{u}) : a = b.
Proof. now destruct a, b. Qed.

Section EraseAdjunctions.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes eo eh ep.
Context {C : Category@{eo eh ep}}.

Program Definition Terminal_Erase_Adjunction (T : @Terminal C) :
  Erase C ⊣ @Diagonal C _1 (@terminal_obj C T) := {|
  adj := fun x y =>
    {| to   := {| morphism := fun _ => @one C T x |}
     ; from := {| morphism := fun _ => ttt |} |}
|}.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.

Program Definition Initial_Erase_Adjunction (I : @Initial C) :
  @Diagonal C _1 (@initial_obj C I) ⊣ Erase C := {|
  adj := fun x y =>
    {| to   := {| morphism := fun _ => ttt |}
     ; from := {| morphism := fun _ => @zero C I y |} |}
|}.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.

End EraseAdjunctions.

Program Definition Erase_right_adjoint_Terminal {C : Category} {R : _1 ⟶ C}
  (A : Erase C ⊣ R) : @Terminal C := {|
  terminal_obj := R ttt;
  one := fun x => to (@adj _1 C (Erase C) R A x ttt) ttt
|}.
Next Obligation.
  rewrite <- (@from_adj_comp_law _1 C (Erase C) R A x ttt f).
  rewrite <- (@from_adj_comp_law _1 C (Erase C) R A x ttt g).
  apply to_adj_respects, one_arrow_eq.
Qed.

Program Definition Erase_left_adjoint_Initial {C : Category} {K : _1 ⟶ C}
  (A : K ⊣ Erase C) : @Initial C := {|
  terminal_obj := K ttt;
  one := fun x => from (@adj C _1 K (Erase C) A ttt x) ttt
|}.
Next Obligation.
  rewrite <- (@to_adj_comp_law C _1 K (Erase C) A ttt x f).
  rewrite <- (@to_adj_comp_law C _1 K (Erase C) A ttt x g).
  apply from_adj_respects, one_arrow_eq.
Qed.

Theorem Erase_right_adjoint_iff_Terminal (C : Category) :
  @Terminal C ↔ { R : _1 ⟶ C & Erase C ⊣ R }.
Proof.
  split.
  - intro T.
    exists (@Diagonal C _1 (@terminal_obj C T)).
    exact (Terminal_Erase_Adjunction T).
  - intros [R A]; exact (Erase_right_adjoint_Terminal A).
Defined.

Theorem Erase_left_adjoint_iff_Initial (C : Category) :
  @Initial C ↔ { K : _1 ⟶ C & K ⊣ Erase C }.
Proof.
  split.
  - intro I.
    exists (@Diagonal C _1 (@initial_obj C I)).
    exact (Initial_Erase_Adjunction I).
  - intros [K A]; exact (Erase_left_adjoint_Initial A).
Defined.

(** The adjoint's value at the unique object IS the (co)terminal object. *)

Example Erase_right_adjoint_value {C : Category} {R : _1 ⟶ C}
  (A : Erase C ⊣ R) :
  @terminal_obj C (Erase_right_adjoint_Terminal A) = R ttt := eq_refl.

Example Erase_left_adjoint_value {C : Category} {K : _1 ⟶ C}
  (A : K ⊣ Erase C) :
  @initial_obj C (Erase_left_adjoint_Initial A) = K ttt := eq_refl.

Example Terminal_Erase_value {C : Category} (T : @Terminal C) :
  fobj[@Diagonal C _1 (@terminal_obj C T)] ttt = @terminal_obj C T := eq_refl.

Example Initial_Erase_value {C : Category} (I : @Initial C) :
  fobj[@Diagonal C _1 (@initial_obj C I)] ttt = @initial_obj C I := eq_refl.

(** The empty shape: limits of shape 0 are exactly terminal objects. *)

Theorem HasLimitsOfShape_0_iff_Terminal (C : Category) :
  HasLimitsOfShape 0 C ↔ @Terminal C.
Proof.
  split.
  - intro H; exact (fst (Terminal_Limit C (From_0 C)) (H (From_0 C))).
  - intros T F; exact (snd (Terminal_Limit C F) T).
Defined.

Corollary Terminal_iff_Diagonal_0_right_adjoint (C : Category) :
  @Terminal C ↔ { R : [0, C] ⟶ C & @Diagonal C 0 ⊣ R }.
Proof.
  split.
  - intro T.
    exact (fst (limits_iff_diagonal_right_adjoint 0 C)
               (snd (HasLimitsOfShape_0_iff_Terminal C) T)).
  - intro H.
    exact (fst (HasLimitsOfShape_0_iff_Terminal C)
               (snd (limits_iff_diagonal_right_adjoint 0 C) H)).
Defined.

(** * Comparison with the right Kan extension along Erase J *)

Section KanComparison.

Context {J C : Category}.

(** The diagonal is the restriction along [Erase J] of the constant
    functor [1 ⟶ C], on both actions and on the nose. *)

Example diagonal_is_induced_obj (c : C) (j : J) :
  fobj[Δ[J](c)] j
    = fobj[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] j := eq_refl.

Example diagonal_is_induced_map (c : C) (x y : J) (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f
    = fmap[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] f := eq_refl.

Program Definition diagonal_induced_iso (c : C) :
  @Isomorphism ([J, C]) (Δ[J](c))
    (fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)) := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.

Context (L : HasLimitsOfShape J C).
Context `{RK : @RightKan J _1 (Erase J) C}.

Corollary lim_Ran_iso (F : J ⟶ C) : lim_obj L F ≅ Ran (Erase J) F ttt.
Proof. exact (@Kan_Limit J C F (L F) RK). Qed.

End KanComparison.

(** * Non-vacuity: the shape 1, and the sandwich at Sets *)

Section OneShapeLimit.

Context {C : Category}.
Context (L : HasLimitsOfShape _1 C).

Program Definition lim_one_acone (F : _1 ⟶ C) : ACone (F ttt) F := {|
  vertex_map := fun x => match x as x' return (F ttt ~{C}~> F x') with
                         | ttt => id
                         end
|}.
Next Obligation.
  destruct x, y, f.
  pose proof (@fmap_id _1 C F ttt) as HI; simpl in HI.
  now rewrite HI, id_left.
Qed.

Definition lim_one_cone (F : _1 ⟶ C) : Cone F :=
  {| vertex_obj := F ttt; coneFrom := lim_one_acone F |}.

Program Definition lim_one_iso (F : _1 ⟶ C) : lim_obj L F ≅ F ttt := {|
  to   := lim_leg L F ttt;
  from := lim_med L (lim_one_cone F)
|}.
Next Obligation. exact (lim_med_commutes L (lim_one_cone F) ttt). Qed.
Next Obligation.
  apply (lim_med_eq L (@limit_cone _1 C F (L F))); intro j; destruct j.
  - rewrite comp_assoc, (lim_med_commutes L (lim_one_cone F) ttt).
    now rewrite id_left.
  - now rewrite id_right.
Qed.

End OneShapeLimit.

Definition Sets_HasLimitsOfShape (J : Category) : HasLimitsOfShape J Sets :=
  Complete_HasLimitsOfShape Sets_Complete J.

Definition Sets_HasColimitsOfShape (J : Category) :
  HasColimitsOfShape J Sets :=
  Cocomplete_HasColimitsOfShape Sets_Cocomplete J.

Definition Sets_Diagonal_Limit_Adjunction (J : Category) :
  @Diagonal Sets J ⊣ LimitFunctor (Sets_HasLimitsOfShape J) :=
  Diagonal_Limit_Adjunction (Sets_HasLimitsOfShape J).

Definition Sets_Colimit_Diagonal_Adjunction (J : Category) :
  ColimitFunctor (Sets_HasColimitsOfShape J) ⊣ @Diagonal Sets J :=
  Colimit_Diagonal_Adjunction (Sets_HasColimitsOfShape J).

Definition DiagBoolSet : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition SetsBoolDiagram : _1 ⟶ Sets := @Diagonal Sets _1 DiagBoolSet.

Definition sets_bool_lim_iso :
  lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram ≅ DiagBoolSet :=
  lim_one_iso (Sets_HasLimitsOfShape _1) SetsBoolDiagram.

Lemma sets_bool_lim_two_elements :
  { a : carrier (lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram)
  & { b : carrier (lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram)
    & a ≈ b → False } }.
Proof.
  exists (from sets_bool_lim_iso true).
  exists (from sets_bool_lim_iso false).
  intro H.
  pose proof (iso_to_from sets_bool_lim_iso true) as H1.
  pose proof (iso_to_from sets_bool_lim_iso false) as H2.
  simpl in H1, H2.
  assert (Hb : (true : carrier DiagBoolSet) ≈ false).
  { transitivity (to sets_bool_lim_iso (from sets_bool_lim_iso true)).
    - symmetry; exact H1.
    - transitivity (to sets_bool_lim_iso (from sets_bool_lim_iso false)).
      + apply (proper_morphism (to sets_bool_lim_iso)); exact H.
      + exact H2. }
  discriminate Hb.
Qed.

(** ** The diagonal preserves limits *)

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DiagonalContinuous.

Context {C J : Category}.
Context {I : Category} (G : I ⟶ C) (N : Cone G) (HN : IsLimitCone N).
Context (M : Cone (@Diagonal C J ◯ G)).

Program Definition diag_eval_cone (j : J) : Cone G := {|
  vertex_obj := fobj[vertex_obj[M]] j;
  coneFrom := {| vertex_map := fun x => transform[cone_leg M x] j |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f j) as Hc.
  simpl in Hc; rewrite <- Hc; reflexivity.
Qed.

Program Definition diag_med :
  vertex_obj[M] ~{[J, C]}~> fobj[@Diagonal C J] (vertex_obj[N]) := {|
  transform := fun j => unique_obj (HN (diag_eval_cone j))
|}.
Next Obligation.
  rewrite id_left.
  apply (uniqueness (HN (diag_eval_cone x))).
  intro i; simpl.
  rewrite comp_assoc.
  rewrite (unique_property (HN (diag_eval_cone y)) i); simpl.
  pose proof (naturality[cone_leg M i] x y f) as Hn; simpl in Hn.
  rewrite <- Hn; apply id_left.
Qed.
Next Obligation.
  rewrite id_left.
  symmetry.
  apply (uniqueness (HN (diag_eval_cone x))).
  intro i; simpl.
  rewrite comp_assoc.
  rewrite (unique_property (HN (diag_eval_cone y)) i); simpl.
  pose proof (naturality[cone_leg M i] x y f) as Hn; simpl in Hn.
  rewrite <- Hn; apply id_left.
Qed.

Lemma diag_med_commutes (i : I) :
  fmap[@Diagonal C J] (cone_leg N i) ∘ diag_med ≈ cone_leg M i.
Proof.
  intro j; simpl.
  exact (unique_property (HN (diag_eval_cone j)) i).
Qed.

Lemma diag_med_unique
  (v : vertex_obj[M] ~{[J, C]}~> fobj[@Diagonal C J] (vertex_obj[N])) :
  (∀ i : I, fmap[@Diagonal C J] (cone_leg N i) ∘ v ≈ cone_leg M i) →
  diag_med ≈ v.
Proof.
  intros Hv j; simpl.
  apply (uniqueness (HN (diag_eval_cone j))).
  intro i; exact (Hv i j).
Qed.

End DiagonalContinuous.

Definition Diagonal_continuous@{jo h o +}
  {C : Category@{o h h}} {J : Category@{jo h h}} :
  ContinuousFunctor (@Diagonal C J).
Proof.
  intros I G N HN M.
  unshelve refine {| unique_obj := diag_med G N HN M |}.
  - exact (diag_med_commutes G N HN M).
  - exact (diag_med_unique G N HN M).
Defined.
