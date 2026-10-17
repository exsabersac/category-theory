(** * Limits over a coproduct of shapes, and connected components *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Initial.
(*
   本文件给出连通分支相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(*
   Book:      Mac Lane, "Categories for the Working Mathematician",
   Book:      Riehl, "Category Theory in Context", §3.6
   nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/limit

   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Part (a): the limit over a coproduct of shapes *)

Section CoproductLimit.

Context {I : Type}.
Context {J : I → Category}.
Context {C : Category}.
Context (F : SigmaCat J ⟶ C).

(* The restriction of [F] to the k-th summand. *)
Definition summand (k : I) : J k ⟶ C := F ◯ SigmaCat_inj J k.

(* Its object and arrow actions are [F]'s at the injected argument, by
   conversion: the injection's own two actions are [(k; x)] and
   [(eq_refl; f)]. *)
Example summand_obj (k : I) (x : J k) : summand k x = F (k; x) := eq_refl.

Example summand_map (k : I) (x y : J k) (f : x ~> y) :
  fmap[summand k] f = fmap[F] ((eq_refl; f) : (k; x) ~{SigmaCat J}~> (k; y))
  := eq_refl.

Context {L : I → C}.
Context (HL : ∀ k : I, IsALimit (summand k) (L k)).

Context {p : C}.
Context {proj : ∀ k : I, p ~> L k}.
Context (HP : IsIndexedProduct L p proj).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coprod_leg (X : SigmaCat J) : p ~> F X :=
  match X as X0 return p ~> F X0 with
  | (k; x) => limit_leg (HL k) x ∘ proj k
  end.

Example coprod_leg_at (k : I) (x : J k) :
  coprod_leg (k; x) = limit_leg (HL k) x ∘ proj k := eq_refl.

Lemma coprod_leg_coherence {X Y : SigmaCat J} (f : X ~> Y) :
  fmap[F] f ∘ coprod_leg X ≈ coprod_leg Y.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  destruct e; simpl in *.
  rewrite comp_assoc.
  now rewrite (limit_leg_coherence (HL i) f).
Qed.

Definition coprod_acone : ACone p F :=
  @Build_ACone (SigmaCat J) C p F coprod_leg (@coprod_leg_coherence).

(** *** Restricting a competing cone to one summand *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition restrict_leg (N : Cone F) (k : I) (x : J k) :
  vertex_obj[N] ~> summand k x := cone_leg N (k; x).

Lemma restrict_coherence (N : Cone F) (k : I) {x y : J k} (f : x ~> y) :
  fmap[summand k] f ∘ restrict_leg N k x ≈ restrict_leg N k y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (k; x) (k; y)
           ((eq_refl; f) : (k; x) ~{SigmaCat J}~> (k; y))).
Qed.

Definition restrict_cone (N : Cone F) (k : I) : Cone (summand k) :=
  @Build_Cone (J k) C (summand k) vertex_obj[N]
    (@Build_ACone (J k) C vertex_obj[N] (summand k)
       (restrict_leg N k) (fun x y f => restrict_coherence N k f)).

(* Its apex is [N]'s, on the nose. *)
Example restrict_cone_apex (N : Cone F) (k : I) :
  vertex_obj[restrict_cone N k] = vertex_obj[N] := eq_refl.

(** *** The mediating morphism *)

(* Mediate summand by summand into the [L k], then tuple across the
   indexed product. *)

Definition coprod_med (N : Cone F) : vertex_obj[N] ~> p :=
  unique_obj (iprod_desc HP (fun k => limit_med (HL k) (restrict_cone N k))).

Lemma coprod_med_proj (N : Cone F) (k : I) :
  proj k ∘ coprod_med N ≈ limit_med (HL k) (restrict_cone N k).
Proof.
  exact (unique_property
           (iprod_desc HP (fun k => limit_med (HL k) (restrict_cone N k))) k).
Qed.

Lemma coprod_med_commutes (N : Cone F) (X : SigmaCat J) :
  coprod_leg X ∘ coprod_med N ≈ cone_leg N X.
Proof.
  destruct X as [k x]; simpl.
  rewrite <- comp_assoc.
  rewrite (coprod_med_proj N k).
  exact (limit_med_commutes (HL k) (restrict_cone N k) x).
Qed.

Lemma coprod_med_unique (N : Cone F) (v : vertex_obj[N] ~> p) :
  (∀ X : SigmaCat J, coprod_leg X ∘ v ≈ cone_leg N X) → coprod_med N ≈ v.
Proof.
  intro Hv.
  apply (uniqueness
           (iprod_desc HP (fun k => limit_med (HL k) (restrict_cone N k)))).
  intro k.
  symmetry.
  apply (limit_med_unique (HL k) (restrict_cone N k)).
  intro x.
  rewrite comp_assoc.
  exact (Hv (k; x)).
Qed.

(** *** The theorem *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coprod_IsALimit : IsALimit F p :=
  @Build_IsALimit (SigmaCat J) C F p coprod_acone
    (fun N => Build_Unique _ _ _ (coprod_med N)
                (coprod_med_commutes N) (coprod_med_unique N)).

(* Its legs ARE [coprod_leg], by conversion. *)
Example coprod_IsALimit_leg (X : SigmaCat J) :
  limit_leg coprod_IsALimit X = coprod_leg X := eq_refl.

(* ... and its mediator IS [coprod_med]. *)
Example coprod_IsALimit_med (N : Cone F) :
  limit_med coprod_IsALimit N = coprod_med N := eq_refl.

Definition coprod_cone : Cone F :=
  @Build_Cone (SigmaCat J) C F p coprod_acone.

Definition coprod_IsLimitCone : IsLimitCone coprod_cone :=
  @ump_limit _ _ _ _ coprod_IsALimit.

Definition coprod_Limit : Limit F := isalimit_to_limit coprod_IsALimit.

(** *** The projections are the restrictions along the injections *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma coprod_proj_is_restriction (k : I) :
  limit_med (HL k) (restrict_cone coprod_cone k) ≈ proj k.
Proof.
  apply (limit_med_unique (HL k) (restrict_cone coprod_cone k)).
  intro x; reflexivity.
Qed.

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma coprod_proj_via_iso {c : C} (Hc : IsALimit F c) (k : I) :
  proj k ∘ to (limit_unique_iso Hc coprod_IsALimit)
    ≈ limit_med (HL k) (restrict_cone (alimit_cone Hc) k).
Proof.
  symmetry.
  apply (limit_med_unique (HL k) (restrict_cone (alimit_cone Hc) k)).
  intro x.
  rewrite comp_assoc.
  exact (fst (limit_unique_iso_legs Hc coprod_IsALimit) (k; x)).
Qed.

(** *** Part (a) packaged as an isomorphism *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coprod_limit_iso {c : C} (Hc : IsALimit F c) : c ≅ p :=
  limit_unique_iso Hc coprod_IsALimit.

Definition coprod_limit_iso_legs {c : C} (Hc : IsALimit F c) :
  (∀ X : SigmaCat J,
     coprod_leg X ∘ to (coprod_limit_iso Hc) ≈ limit_leg Hc X) *
  (∀ X : SigmaCat J,
     limit_leg Hc X ∘ from (coprod_limit_iso Hc) ≈ coprod_leg X) :=
  limit_unique_iso_legs Hc coprod_IsALimit.

Theorem coprod_limit_iso_unique {c : C} (Hc : IsALimit F c)
  (h : c ~{C}~> p) :
  (∀ X : SigmaCat J, coprod_leg X ∘ h ≈ limit_leg Hc X) →
  h ≈ to (coprod_limit_iso Hc).
Proof. exact (limit_unique_iso_unique Hc coprod_IsALimit h). Qed.

End CoproductLimit.

Arguments summand {I J C} F k.
Arguments coprod_leg {I J C} F {L} HL {p proj} X.
Arguments coprod_IsALimit {I J C} F {L} HL {p proj} HP.

(** *** The bundled readings *)

(* Over a category with all indexed products the hypothesis [HP]
   disappears.  [HasIndexedProducts] is stated over [IsIndexedProduct],
   so this reading carries no [Set] pin either. *)

Definition coprod_IsALimit_HasIndexedProducts {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C) (HIP : HasIndexedProducts C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k)) :
  IsALimit F (indexed_product L) :=
  coprod_IsALimit F HL (indexed_product_ump L).

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coprod_IsALimit_iprod {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k))
  (P : Limit (DiscreteCat_Functor L)) : IsALimit F (iprod L P) :=
  coprod_IsALimit F HL (limit_is_indexed_product L P).

Definition coprod_Limit_iprod {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k))
  (P : Limit (DiscreteCat_Functor L)) : Limit F :=
  isalimit_to_limit (coprod_IsALimit_iprod F HL P).

(* The [iprod] corollary's legs are the general ones at [iprod_proj], by
   conversion -- so the corollary is the theorem instantiated, not a
   parallel construction. *)

Example coprod_IsALimit_iprod_leg {I : Type} {J : I → Category}
  {C : Category} (F : SigmaCat J ⟶ C)
  {L : I → C} (HL : ∀ k : I, IsALimit (summand F k) (L k))
  (P : Limit (DiscreteCat_Functor L)) (k : I) (x : J k) :
  limit_leg (coprod_IsALimit_iprod F HL P) (k; x)
    = limit_leg (HL k) x ∘ iprod_proj L P k := eq_refl.

(** ** Part (b): the decomposition of a category into its components *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record ComponentDecomposition (C : Category) := {
  cd_index : Type;
  cd_rep   : cd_index → C;
  cd_part  : C → cd_index;
  cd_join  : ∀ x : C, ZigZag (cd_rep (cd_part x)) x;
  cd_sep   : ∀ (x : C) (k : cd_index), ZigZag (cd_rep k) x → cd_part x = k
}.

Arguments cd_index {_} _.
Arguments cd_rep {_} _.
Arguments cd_part {_} _.
Arguments cd_join {_} _.
Arguments cd_sep {_} _.

Section DecompositionTheory.

Context {C : Category}.
Variable D : ComponentDecomposition C.

(* Choosing a representative and reading off its index is the identity. *)
Definition cd_part_rep (k : cd_index D) : cd_part D (cd_rep D k) = k :=
  cd_sep D (cd_rep D k) k (zz_nil _).

(* Joined objects lie in the same component. *)
Definition cd_part_zigzag {x y : C} (s : ZigZag x y) :
  cd_part D x = cd_part D y :=
  eq_sym (cd_sep D y (cd_part D x) (zigzag_trans (cd_join D x) s)).

(* ... and conversely, which is the other half of "the parts ARE the
   components".  This direction consumes no [cd_sep]. *)
Definition cd_conn {x y : C} (e : cd_part D x = cd_part D y) : ZigZag x y :=
  zigzag_trans
    (match e in _ = k return ZigZag x (cd_rep D k) with
     | eq_refl => zigzag_sym (cd_join D x)
     end)
    (cd_join D y).

(** *** The summands, the coproduct, and the comparison functor *)

Definition cd_comp (k : cd_index D) : Category :=
  ConnectedComponent C (cd_rep D k).

Definition cd_sum : Category := SigmaCat cd_comp.

Definition cd_compare : cd_sum ⟶ C :=
  SigmaCat_case (fun k => Component_Incl C (cd_rep D k)).

(* Each summand is connected -- the donor's own theorem, instantiated. *)
Definition cd_comp_Connected (k : cd_index D) : Connected (cd_comp k) :=
  Component_Connected C (cd_rep D k).

(* Both actions of the comparison are the evident projections, by
   conversion. *)
Example cd_compare_obj (k : cd_index D) (a : cd_comp k) :
  cd_compare (k; a) = `1 a := eq_refl.

Example cd_compare_map (k : cd_index D) (a b : cd_comp k) (f : a ~> b) :
  fmap[cd_compare] ((eq_refl; f) : (k; a) ~{cd_sum}~> (k; b)) = `1 f
  := eq_refl.

(** *** The comparison is essentially surjective, with NO hypothesis *)

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cd_eso_obj (y : C) : cd_sum :=
  (cd_part D y; ((y; cd_join D y) : cd_comp (cd_part D y))).

Example cd_eso_obj_image (y : C) : cd_compare (cd_eso_obj y) = y := eq_refl.

Definition cd_compare_ESO : EssentiallySurjective cd_compare :=
  @Build_EssentiallySurjective cd_sum C cd_compare cd_eso_obj
    (fun y => iso_id).

(** *** The comparison is full, with NO hypothesis *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cd_full_eq {X Y : cd_sum} (f : cd_compare X ~> cd_compare Y) :
  `1 X = `1 Y :=
  eq_trans (eq_sym (cd_sep D (`1 (`2 X)) (`1 X) (`2 (`2 X))))
    (eq_trans (cd_part_zigzag (hom_zigzag f))
              (cd_sep D (`1 (`2 Y)) (`1 Y) (`2 (`2 Y)))).

(* Given ANY index equality, the arrow lifts.  The equality is a
   universally quantified variable here, which is exactly what makes
   [destruct e] available and every transport vanish. *)

Lemma cd_full_step {X Y : cd_sum} (e : `1 X = `1 Y)
  (f : cd_compare X ~> cd_compare Y) :
  ∃ g : ob_cast cd_comp e (`2 X) ~> `2 Y,
    fmap[cd_compare] ((e; g) : X ~{cd_sum}~> Y) ≈ f.
Proof.
  destruct X as [k a], Y as [l b]; simpl in *.
  destruct e; simpl in *.
  destruct a as [x sx], b as [y sy]; simpl in *.
  exists (component_arr sx sy f).
  reflexivity.
Defined.

Definition cd_compare_Full : Functor.Full cd_compare := {|
  prefmap := fun X Y f =>
    ((cd_full_eq f; `1 (cd_full_step (cd_full_eq f) f)) : X ~{cd_sum}~> Y);
  fmap_sur := fun X Y f => `2 (cd_full_step (cd_full_eq f) f)
|}.

(** *** Faithfulness, and the one hypothesis the file spends *)

Lemma cd_faithful_step {X Y : cd_sum} (e1 e2 : `1 X = `1 Y) (p : e1 = e2)
  (g1 : ob_cast cd_comp e1 (`2 X) ~> `2 Y)
  (g2 : ob_cast cd_comp e2 (`2 X) ~> `2 Y) :
  fmap[cd_compare] ((e1; g1) : X ~{cd_sum}~> Y)
    ≈ fmap[cd_compare] ((e2; g2) : X ~{cd_sum}~> Y) →
  mor_cast cd_comp p g1 ≈ g2.
Proof.
  destruct X as [k a], Y as [l b]; simpl in *.
  destruct p; destruct e1; simpl in *.
  intro H; exact H.
Qed.

(* [IdxUIP] is the donor's own hypothesis (Construction/Coproduct/
   Indexed.v), and it is spent HERE AND NOWHERE ELSE in this file. *)

Definition cd_compare_Faithful (U : IdxUIP (cd_index D)) :
  Functor.Faithful cd_compare :=
  @Build_Faithful cd_sum C cd_compare
    (fun (X Y : cd_sum) (f g : X ~{cd_sum}~> Y) H =>
       (IdxUIP_pair U (`1 f) (`1 g);
        cd_faithful_step (`1 f) (`1 g) (IdxUIP_pair U (`1 f) (`1 g))
          (`2 f) (`2 g) H)).

(*
   本节说明等价、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cd_equivalence (U : IdxUIP (cd_index D)) :
  EquivalenceOfCategories cd_compare :=
  @FF_ESO_Equivalence cd_sum C cd_compare
    cd_compare_Full (cd_compare_Faithful U) cd_compare_ESO.

(* The bundled reading, in the vocabulary Theory/Skeleton.v uses for the
   analogous statement about skeletons. *)

Definition cd_bundled_equivalence (U : IdxUIP (cd_index D)) : cd_sum ≃ C :=
  (cd_compare; cd_equivalence U).

End DecompositionTheory.

(** ** Riehl's uniqueness clause for the decomposition *)

(* Transport an index of one decomposition to an index of another, by
   reading off the part of its chosen representative. *)

Definition cd_transfer {C : Category} (D D' : ComponentDecomposition C)
  (k : cd_index D) : cd_index D' := cd_part D' (cd_rep D k).

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cd_transfer_round {C : Category} (D D' : ComponentDecomposition C)
  (k : cd_index D) : cd_transfer D' D (cd_transfer D D' k) = k.
Proof.
  unfold cd_transfer.
  transitivity (cd_part D (cd_rep D k)).
  - exact (cd_part_zigzag D (cd_join D' (cd_rep D k))).
  - exact (cd_part_rep D k).
Qed.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cd_transfer_part {C : Category} (D D' : ComponentDecomposition C)
  (y : C) : cd_transfer D D' (cd_part D y) = cd_part D' y.
Proof. exact (cd_part_zigzag D' (cd_join D y)). Qed.

(* ... and it carries representatives to joined representatives. *)

Definition cd_transfer_join {C : Category} (D D' : ComponentDecomposition C)
  (k : cd_index D) :
  ZigZag (cd_rep D' (cd_transfer D D' k)) (cd_rep D k) :=
  cd_join D' (cd_rep D k).

(** ** Limits along a full, essentially surjective functor of shapes *)

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section LimitAlongFullESO.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Set Default Proof Using "All".

Context {K J C : Category}.
Context (Phi : K ⟶ J).
Context (PF : Functor.Full Phi).
Context (PE : EssentiallySurjective Phi).

#[local] Existing Instance PF.
#[local] Existing Instance PE.

Context (G : J ⟶ C).
Context {c : C}.
Context (H : IsALimit (G ◯ Phi) c).

Definition xfer_leg (y : J) : c ~> G y :=
  fmap[G] (to (eso_iso y)) ∘ limit_leg H (eso_obj y).

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma xfer_leg_image (z : K) : xfer_leg (Phi z) ≈ limit_leg H z.
Proof.
  unfold xfer_leg.
  transitivity (fmap[G] (fmap[Phi] (prefmap (to (eso_iso (Phi z)))))
                  ∘ limit_leg H (eso_obj (Phi z))).
  - now rewrite (fmap_sur (to (eso_iso (Phi z)))).
  - exact (limit_leg_coherence H (prefmap (to (eso_iso (Phi z))))).
Qed.

Lemma xfer_coherence {y z : J} (f : y ~> z) :
  fmap[G] f ∘ xfer_leg y ≈ xfer_leg z.
Proof.
  unfold xfer_leg.
  pose (g := from (eso_iso z) ∘ f ∘ to (eso_iso y)).
  assert (Hg : f ∘ to (eso_iso y) ≈ to (eso_iso z) ∘ g).
  { unfold g; rewrite !comp_assoc, iso_to_from, id_left; reflexivity. }
  assert (Hleg : fmap[G] g ∘ limit_leg H (eso_obj y)
                   ≈ limit_leg H (eso_obj z)).
  { transitivity (fmap[G] (fmap[Phi] (prefmap g)) ∘ limit_leg H (eso_obj y)).
    - now rewrite (fmap_sur g).
    - exact (limit_leg_coherence H (prefmap g)). }
  rewrite comp_assoc, <- fmap_comp, Hg, fmap_comp, <- comp_assoc.
  now rewrite Hleg.
Qed.

Definition xfer_acone : ACone c G :=
  @Build_ACone J C c G xfer_leg (@xfer_coherence).

(* A cone over [G] restricts along [Phi] to a cone over [G ◯ Phi]; the
   coherence proof is the given cone's own, at the [Phi]-image arrow. *)

Definition xfer_restrict (N : Cone G) : Cone (G ◯ Phi) :=
  @Build_Cone K C (G ◯ Phi) vertex_obj[N]
    (@Build_ACone K C vertex_obj[N] (G ◯ Phi)
       (fun z => cone_leg N (Phi z))
       (fun z w h => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N)
                       (Phi z) (Phi w) (fmap[Phi] h))).

(* Deliberately unascribed: writing the type as [vertex_obj[N] ~> c]
   would make the composite below carry a different (though convertible)
   object argument, and setoid rewriting matches syntactically. *)
Definition xfer_med (N : Cone G) := limit_med H (xfer_restrict N).

Lemma xfer_med_commutes (N : Cone G) (y : J) :
  xfer_leg y ∘ xfer_med N ≈ cone_leg N y.
Proof.
  transitivity (fmap[G] (to (eso_iso y)) ∘ cone_leg N (Phi (eso_obj y))).
  - unfold xfer_leg, xfer_med.
    rewrite <- comp_assoc.
    apply compose_respects; [ reflexivity |].
    exact (limit_med_commutes H (xfer_restrict N) (eso_obj y)).
  - exact (@cone_coherence J C vertex_obj[N] G (@coneFrom J C G N)
             (Phi (eso_obj y)) y (to (eso_iso y))).
Qed.

Lemma xfer_med_unique (N : Cone G) (v : vertex_obj[N] ~> c) :
  (∀ y : J, xfer_leg y ∘ v ≈ cone_leg N y) → xfer_med N ≈ v.
Proof.
  intro Hv.
  apply (limit_med_unique H (xfer_restrict N)).
  intro z.
  rewrite <- (xfer_leg_image z).
  exact (Hv (Phi z)).
Qed.

Definition xfer_IsALimit : IsALimit G c :=
  @Build_IsALimit J C G c xfer_acone
    (fun N => Build_Unique _ _ _ (xfer_med N)
                (xfer_med_commutes N) (xfer_med_unique N)).

End LimitAlongFullESO.

(** ** Part (c): every limit is a product of limits over connected shapes *)

Section ComponentLimit.

Context {J C : Category}.
Variable D : ComponentDecomposition J.
Variable F : J ⟶ C.

(* The diagram restricted to the k-th connected component. *)
Definition component_diagram (k : cd_index D) : cd_comp D k ⟶ C :=
  F ◯ Component_Incl J (cd_rep D k).

(* It agrees with the k-th summand of the reindexed diagram on BOTH
   actions, by conversion... *)

Example component_diagram_obj (k : cd_index D) (a : cd_comp D k) :
  component_diagram k a = summand (F ◯ cd_compare D) k a := eq_refl.

Example component_diagram_map (k : cd_index D) (a b : cd_comp D k)
  (f : a ~> b) :
  fmap[component_diagram k] f = fmap[summand (F ◯ cd_compare D) k] f
  := eq_refl.

(* ... but the two functor RECORDS are not identified: [Compose] rebuilds
   its three law fields, and they are distinct opaque terms.  Measured,
   not assumed. *)

Fail Example component_diagram_strict (k : cd_index D) :
  component_diagram k = summand (F ◯ cd_compare D) k := eq_refl.

(* So the comparison is made at [≈], with identity components -- which is
   all the two definitional agreements above leave to prove. *)

Definition component_diagram_equiv (k : cd_index D) :
  component_diagram k ≈ summand (F ◯ cd_compare D) k.
Proof.
  exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Defined.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition components_IsALimit {L : cd_index D → C}
  (HL : ∀ k : cd_index D, IsALimit (component_diagram k) (L k))
  {p : C} {proj : ∀ k : cd_index D, p ~> L k}
  (HP : IsIndexedProduct L p proj) : IsALimit F p :=
  xfer_IsALimit (cd_compare D) (cd_compare_Full D) (cd_compare_ESO D) F
    (coprod_IsALimit (F ◯ cd_compare D)
       (fun k => isalimit_transport (component_diagram_equiv k) (HL k)) HP).

Definition components_Limit {L : cd_index D → C}
  (HL : ∀ k : cd_index D, IsALimit (component_diagram k) (L k))
  {p : C} {proj : ∀ k : cd_index D, p ~> L k}
  (HP : IsIndexedProduct L p proj) : Limit F :=
  isalimit_to_limit (components_IsALimit HL HP).

(* The bundled reading over a category with all indexed products. *)

Definition components_IsALimit_HasIndexedProducts (HIP : HasIndexedProducts C)
  {L : cd_index D → C}
  (HL : ∀ k : cd_index D, IsALimit (component_diagram k) (L k)) :
  IsALimit F (indexed_product L) :=
  components_IsALimit HL (indexed_product_ump L).

End ComponentLimit.

(** ** Non-vacuity, part 1: the connected (one-component) case *)

(* The walking arrow is connected, though NOT by a single arrow in either
   direction -- there is no [TwoY ~> TwoX] -- so the zig-zag really is
   used. *)

Definition two_ZigZag (x y : _2) : ZigZag x y.
Proof.
  destruct x, y.
  - exact (zz_nil _).
  - exact (hom_zigzag (TwoXY : TwoX ~{_2}~> TwoY)).
  - exact (zigzag_sym (hom_zigzag (TwoXY : TwoX ~{_2}~> TwoY))).
  - exact (zz_nil _).
Defined.

Definition Two_Connected : Connected _2 := two_ZigZag.

Definition Two_Decomposition : ComponentDecomposition _2 :=
  @Build_ComponentDecomposition _2 poly_unit
    (fun _ => TwoX) (fun _ => ttt)
    (fun x => two_ZigZag TwoX x)
    (fun x k s => match k as k0 return ttt = k0 with ttt => eq_refl end).

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example Two_Decomposition_index : cd_index Two_Decomposition = poly_unit
  := eq_refl.

(* [poly_unit_IdxUIP] is the DONOR's (Construction/Coproduct/Indexed.v),
   not a second copy. *)

Definition Two_cd_equivalence :
  EquivalenceOfCategories (cd_compare Two_Decomposition) :=
  cd_equivalence Two_Decomposition poly_unit_IdxUIP.

(* The one component is not itself trivial: it contains both objects of
   [_2], with the non-identity arrow between them. *)

Definition Two_component_TwoX : cd_comp Two_Decomposition ttt :=
  Component_obj _2 TwoX.

Definition Two_component_TwoY : cd_comp Two_Decomposition ttt :=
  existT _ TwoY (two_ZigZag TwoX TwoY).

Definition Two_component_arrow :
  Two_component_TwoX ~{cd_comp Two_Decomposition ttt}~> Two_component_TwoY :=
  @component_arr _2 TwoX TwoX TwoY (@zz_nil _2 TwoX)
    (two_ZigZag TwoX TwoY) TwoXY.

Lemma Two_component_objects_differ : TwoX <> TwoY.
Proof. discriminate. Qed.

(** ** Non-vacuity, part 2: a shape with two components *)

(* Along a zig-zag in a coproduct of categories the index never moves:
   every step carries an index equality, and the chain composes them. *)

Fixpoint sigma_index_zigzag {I : Type} {Cs : I → Category}
  {X Y : SigmaCat Cs} (s : ZigZag X Y) : `1 X = `1 Y :=
  match s in ZigZag a b return `1 a = `1 b with
  | zz_nil _    => eq_refl
  | zz_fwd f s' => eq_trans (`1 f) (sigma_index_zigzag s')
  | zz_bwd f s' => eq_trans (eq_sym (`1 f)) (sigma_index_zigzag s')
  end.

(* Two disjoint copies of the walking arrow. *)

Definition TwoSum : Category := SigmaCat (fun _ : bool => _2).

Definition twosum_arr (X : TwoSum) : ((`1 X; TwoX) : TwoSum) ~> X :=
  (eq_refl; match `2 X as o return TwoX ~{_2}~> o with
            | TwoX => id
            | TwoY => TwoXY
            end).

Definition TwoSum_Decomposition : ComponentDecomposition TwoSum :=
  @Build_ComponentDecomposition TwoSum bool
    (fun k => ((k; TwoX) : TwoSum)) (fun X => `1 X)
    (fun X => hom_zigzag (twosum_arr X))
    (fun X k s => eq_sym (sigma_index_zigzag s)).

(* THE DECOMPOSITION IS NOT DEGENERATE, AND THIS IS PROVED RATHER THAN
   ASSERTED.  The two summands are genuinely separated: no zig-zag joins
   a point of one to a point of the other. *)

Theorem TwoSum_separated :
  ZigZag ((true; TwoX) : TwoSum) ((false; TwoX) : TwoSum) → False.
Proof. intro s; exact (Bool.diff_true_false (sigma_index_zigzag s)). Qed.

Corollary TwoSum_not_connected : Connected TwoSum → False.
Proof. intro K; exact (TwoSum_separated (K _ _)). Qed.

(* ... and neither summand is a point: each contains both objects of the
   walking arrow, which are distinct in [TwoSum]. *)

Definition twosum_snd (X : TwoSum) : bool :=
  match `2 X with TwoX => true | TwoY => false end.

Theorem TwoSum_component_objects_differ (k : bool) :
  ((k; TwoX) : TwoSum) <> (k; TwoY).
Proof.
  intro e.
  exact (Bool.diff_true_false (f_equal twosum_snd e)).
Qed.

Example TwoSum_component_TwoY (k : bool) : cd_comp TwoSum_Decomposition k :=
  (((k; TwoY) : TwoSum); hom_zigzag (twosum_arr (k; TwoY))).

Definition bool_IdxUIP : IdxUIP bool :=
  fun i p => UIP_dec Bool.bool_dec p eq_refl.

Definition TwoSum_cd_equivalence :
  EquivalenceOfCategories (cd_compare TwoSum_Decomposition) :=
  cd_equivalence TwoSum_Decomposition bool_IdxUIP.

(** ** Why the index cannot simply be π₀ *)

(* A coproduct of categories over an index with two distinct inhabited
   summands is never connected -- the index cannot move along a chain. *)

Definition SigmaCat_not_connected {I : Type} {Cs : I → Category}
  {i j : I} (Hij : i = j → False) (x : Cs i) (y : Cs j) :
  Connected (SigmaCat Cs) → False :=
  fun K => Hij (sigma_index_zigzag
                  (K ((i; x) : SigmaCat Cs) ((j; y) : SigmaCat Cs))).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition naive_pi0_sum : Category :=
  SigmaCat (fun x : carrier (pi0 _2) => ConnectedComponent _2 x).

Definition naive_pi0_sum_not_connected : Connected naive_pi0_sum → False :=
  SigmaCat_not_connected Two_component_objects_differ
    (Component_obj _2 TwoX) (Component_obj _2 TwoY).

(* Consequently no functor out of [_2] hits it up to isomorphism: the
   naive index does not merely name the components badly, it names a
   category that no comparison from [_2] can cover. *)

Definition no_ESO_into_naive_pi0_sum (F : _2 ⟶ naive_pi0_sum) :
  EssentiallySurjective F → False :=
  fun E => naive_pi0_sum_not_connected (eso_connected F E Two_Connected).

(** ** Non-vacuity, part 3: part (a) computing in [Coq] *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coq_point (T : Type) : _1 ⟶ Coq :=
  @Build_Functor _1 Coq (fun _ => T) (fun _ _ _ => Datatypes.id)
    (fun _ _ _ _ _ _ => eq_refl) (fun _ _ => eq_refl)
    (fun _ _ _ _ _ _ => eq_refl).

(* A diagram over the coproduct of two points, picking out [nat] and
   [bool].  It is built by the DONOR's case functor, so it carries no
   proof obligation of its own. *)

Definition CoqPair : SigmaCat (fun _ : bool => _1) ⟶ Coq :=
  SigmaCat_case (fun k : bool => coq_point (if k then nat else bool)).

Definition coqpair_fam (k : bool) : Coq := if k then nat else bool.

Definition coqpair_obj : Coq := (nat * bool)%type.

Definition coqpair_proj (k : bool) : coqpair_obj ~{Coq}~> coqpair_fam k :=
  match k as k0 return coqpair_obj → coqpair_fam k0 with
  | true  => @fst nat bool
  | false => @snd nat bool
  end.

Definition coqpair_IsIndexedProduct :
  IsIndexedProduct coqpair_fam coqpair_obj coqpair_proj.
Proof.
  constructor; intros c pi.
  unshelve eapply Build_Unique.
  - exact (fun x => (pi true x, pi false x)).
  - intros [|] x; reflexivity.
  - intros v Hv x.
    pose proof (Hv true x) as H1; pose proof (Hv false x) as H2.
    simpl in H1, H2.
    destruct (v x); simpl in *; subst; reflexivity.
Defined.

(* Each summand's limit is the point's: the diagram restricted to a
   summand is a functor out of [_1], and [point_IsALimit] applies. *)

Definition coqpair_summand_limit (k : bool) :
  IsALimit (summand CoqPair k) (coqpair_fam k) :=
  point_IsALimit (summand CoqPair k).

Definition CoqPair_IsALimit : IsALimit CoqPair coqpair_obj :=
  coprod_IsALimit CoqPair coqpair_summand_limit coqpair_IsIndexedProduct.

(* The legs COMPUTE to the two projections. *)

Example CoqPair_leg_true (x : nat * bool) :
  limit_leg CoqPair_IsALimit ((true; ttt) : SigmaCat (fun _ : bool => _1)) x
    = fst x := eq_refl.

Example CoqPair_leg_false (x : nat * bool) :
  limit_leg CoqPair_IsALimit ((false; ttt) : SigmaCat (fun _ : bool => _1)) x
    = snd x := eq_refl.

(* ... and so does the mediator, at a cone that is not a projection pair:
   [n] goes to [(n, n =? 0)]. *)

Definition coq_test_leg (X : SigmaCat (fun _ : bool => _1)) :
  nat ~{Coq}~> CoqPair X :=
  match `1 X as k return nat → coqpair_fam k with
  | true  => fun n => n
  | false => fun n => Nat.eqb n 0
  end.

Lemma coq_test_coherence {X Y : SigmaCat (fun _ : bool => _1)} (f : X ~> Y) :
  fmap[CoqPair] f ∘ coq_test_leg X ≈ coq_test_leg Y.
Proof.
  destruct X as [k x], Y as [l y], f as [e m]; simpl in *.
  destruct e; simpl in *.
  destruct k; intro n; reflexivity.
Qed.

Definition coq_test_cone : Cone CoqPair :=
  @Build_Cone (SigmaCat (fun _ : bool => _1)) Coq CoqPair nat
    (@Build_ACone (SigmaCat (fun _ : bool => _1)) Coq nat CoqPair
       coq_test_leg (@coq_test_coherence)).

Example CoqPair_med_computes (n : nat) :
  limit_med CoqPair_IsALimit coq_test_cone n = (n, Nat.eqb n 0) := eq_refl.

(* The witness is not degenerate: the two summand limits are different
   objects, and the apex has at least two distinct elements. *)

Lemma coqpair_fam_differ : coqpair_fam true <> coqpair_fam false.
Proof.
  intro e.
  assert (K : ∀ x y z : coqpair_fam false, x = y \/ y = z \/ x = z)
    by (simpl; intros [|] [|] [|]; auto).
  rewrite <- e in K.
  destruct (K 0%nat 1%nat 2%nat) as [H|[H|H]]; discriminate.
Qed.

Example CoqPair_apex_two_elements : (0%nat, true) <> (0%nat, false).
Proof. discriminate. Qed.

(** ** Measured boundaries, pinned *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniversePin.

Universe uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).
Context (Js : bool → Category@{uo uh uh}).

(* Controls: the elementary vocabulary is formable at these levels. *)

Check (fun (A : Type) (f : A → Cu) (p : Cu) (pr : ∀ a : A, p ~{Cu}~> f a) =>
         IsIndexedProduct f p pr).

Check (fun (F : SigmaCat Js ⟶ Cu) (p : Cu) => IsALimit F p).

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (p : Cu) (pr : ∀ k : bool, p ~{Cu}~> L k)
           (HP : IsIndexedProduct L p pr) => coprod_IsALimit F HL HP).

(* The donor's product operator IS formable here. *)

Check (fun (A : Type) (f : A → Cu)
           (P : Limit (DiscreteCat_Functor f)) => iprod f P).

(* ... and so, therefore, is the corollary stated over it. *)

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (P : Limit (DiscreteCat_Functor L)) =>
         coprod_IsALimit_iprod F HL P).

End UniversePin.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example sigma_obj_eta (I : Type) (Cs : I → Category)
  (X : SigmaCat Cs) : X = ((`1 X; `2 X) : SigmaCat Cs) := eq_refl.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example sigma_hom_eta (I : Type) (Cs : I → Category)
  {X Y : SigmaCat Cs} (f : X ~> Y) :
  sigma_equiv f ((`1 f; `2 f) : X ~{SigmaCat Cs}~> Y)
    = sigma_equiv f f := eq_refl.
