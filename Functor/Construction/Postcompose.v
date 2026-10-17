Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Theory.Bicategory.
Require Import Category.Instance.Cat.Bicategory.

Generalizable All Variables.

(** * Postcomposition, and the invariance of naturality under enlargement *)

(*
   nLab:      https://ncatlab.org/nlab/show/full+subcategory
   nLab:      https://ncatlab.org/nlab/show/whiskering
   Wikipedia: https://en.wikipedia.org/wiki/Full_subcategory

   本文件给出后复合构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The transformation setoid, named *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition NatSetoid {A B : Category} (K L : A ⟶ B) : SetoidObject :=
  {| carrier   := K ~{[A, B]}~> L
   ; is_setoid := @homset ([A, B]) K L |}.

Example nat_setoid_is_Transform_Setoid {A B : Category} (K L : A ⟶ B) :
  @homset ([A, B]) K L = @Transform_Setoid A B K L := eq_refl.

(** ** The postcomposition functor *)

Section Postcompose.

Universes do dh dp eo eh ep fo fh fp.

Context {D : Category@{do dh dp}}.
Context {E : Category@{eo eh ep}}.
Context {E' : Category@{fo fh fp}}.
Context (J : E ⟶ E').

#[local] Obligation Tactic := idtac.

(*
   本节说明 Postcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Postcompose : [D, E] ⟶ [D, E'] := {|
  fobj := fun K => J ◯ K;
  fmap := fun K L θ => J ⊳ θ
|}.
Next Obligation.
  simpl; intros K L θ θ' Hθ x; apply fmap_respects; exact (Hθ x).
Qed.
Next Obligation.
  simpl; intros K x; reflexivity.
Qed.
Next Obligation.
  simpl; intros K L M θ θ' x; apply fmap_comp.
Qed.

(* Both actions on the nose. *)
Example postcompose_fobj (K : D ⟶ E) : fobj[Postcompose] K = J ◯ K := eq_refl.

Example postcompose_fmap (K L : D ⟶ E) (θ : K ⟹ L) :
  fmap[Postcompose] θ = J ⊳ θ := eq_refl.

Example postcompose_fmap_component (K L : D ⟶ E) (θ : K ⟹ L) (x : D) :
  transform[fmap[Postcompose] θ] x = fmap[J] (transform[θ] x) := eq_refl.

(** ** Faithfulness *)

(* Componentwise injectivity of [fmap[J]] is componentwise injectivity of
   the whiskering, and the hom-setoid of a functor category is
   componentwise, so there is nothing else to check. *)
Lemma Postcompose_Faithful : Faithful J → Faithful Postcompose.
Proof.
  intro JF; constructor; simpl; intros K L θ θ' Hθ x.
  apply (@fmap_inj _ _ J JF).
  exact (Hθ x).
Qed.

End Postcompose.

Arguments Postcompose {D E E'} J.

(** ** Fullness, and the Nat-setoid isomorphism *)

Section PostcomposeFullyFaithful.

Universes do dh dp eo eh ep fo fh fp.

Context {D : Category@{do dh dp}}.
Context {E : Category@{eo eh ep}}.
Context {E' : Category@{fo fh fp}}.
Context (J : E ⟶ E').
Context (JFull : Full J).
Context (JFaith : Faithful J).

#[local] Obligation Tactic := idtac.

(*
   本节说明 Postcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition post_prefmap {K L : D ⟶ E} (φ : J ◯ K ⟹ J ◯ L) :
  K ⟹ L := {|
  transform := fun x => @prefmap _ _ J JFull (K x) (L x) (transform[φ] x)
|}.
Next Obligation.
  intros K L φ x y f; simpl.
  apply (@fmap_inj _ _ J JFaith).
  rewrite !fmap_comp, !fmap_sur.
  exact (@naturality _ _ _ _ φ x y f).
Qed.
Next Obligation.
  intros K L φ x y f; simpl.
  apply (@fmap_inj _ _ J JFaith).
  rewrite !fmap_comp, !fmap_sur.
  exact (@naturality_sym _ _ _ _ φ x y f).
Qed.

(* The section law is J's own, applied at each component. *)
Program Definition Postcompose_Full : Full (Postcompose (D:=D) J) := {|
  prefmap := fun K L φ => post_prefmap φ
|}.
Next Obligation.
  simpl; intros K L φ x; apply fmap_sur.
Qed.

(*
   本节说明 Postcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition postcompose_hom_iso (K L : D ⟶ E) :
  @Isomorphism Sets (NatSetoid K L) (NatSetoid (J ◯ K) (J ◯ L)) := {|
  to   := {| morphism := fun θ => J ⊳ θ |};
  from := {| morphism := fun φ => post_prefmap φ |}
|}.
Next Obligation.
  intros K L θ θ' Hθ x; simpl; apply fmap_respects; exact (Hθ x).
Qed.
Next Obligation.
  intros K L φ φ' Hφ x; simpl.
  apply (@fmap_inj _ _ J JFaith).
  rewrite !fmap_sur.
  exact (Hφ x).
Qed.
Next Obligation.
  intros K L φ x; simpl; apply fmap_sur.
Qed.
Next Obligation.
  intros K L θ x; simpl.
  apply (@fmap_inj _ _ J JFaith).
  apply fmap_sur.
Qed.

(* The two legs, on the nose. *)
Example postcompose_hom_iso_to (K L : D ⟶ E) (θ : K ⟹ L) :
  to (postcompose_hom_iso K L) θ = J ⊳ θ := eq_refl.

Example postcompose_hom_iso_from (K L : D ⟶ E) (φ : J ◯ K ⟹ J ◯ L) :
  from (postcompose_hom_iso K L) φ = post_prefmap φ := eq_refl.

(* The forward leg IS the functor's own action on 2-cells; this is the
   sentence "the isomorphism is [Postcompose J] restricted to a hom-setoid",
   machine-checked rather than asserted. *)
Example postcompose_hom_iso_to_is_fmap (K L : D ⟶ E) (θ : K ⟹ L) :
  to (postcompose_hom_iso K L) θ = fmap[Postcompose J] θ := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition postcompose_nat_bijection (K L : D ⟶ E) :
  (K ⟹ L) ≊ (J ◯ K ⟹ J ◯ L) := postcompose_hom_iso K L.

End PostcomposeFullyFaithful.

Arguments post_prefmap {D E E'} J JFull JFaith {K L} φ.
Arguments Postcompose_Full {D E E'} J JFull JFaith.
Arguments postcompose_hom_iso {D E E'} J JFull JFaith K L.
Arguments postcompose_nat_bijection {D E E'} J JFull JFaith K L.

(** ** Comparison with the horizontal-composition bifunctor *)

Section ViaHcompose.

Context {D E E' : Category}.
Context (J : E ⟶ E').

#[local] Obligation Tactic := idtac.

(* The postcomposition functor that the tree already had, assembled: freeze
   the first argument of horizontal composition at J. *)
Definition PostcomposeViaHcompose : [D, E] ⟶ [D, E'] :=
  Partial_r (@Cat_Hcompose D E E') J.

(* The object actions agree definitionally. *)
Example postcompose_via_hcompose_obj (K : D ⟶ E) :
  fobj[PostcomposeViaHcompose] K = fobj[Postcompose J] K := eq_refl.

(*
   本节说明 Postcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example postcompose_via_hcompose_component
        (K L : D ⟶ E) (θ : K ⟹ L) (x : D) :
  transform[fmap[PostcomposeViaHcompose] θ] x
    = fmap[J] (@id E (L x)) ∘ fmap[J] (transform[θ] x) := eq_refl.

(* Up to `≈` the two agree, the unit being discharged by [fmap_id]. *)
Lemma postcompose_via_hcompose_fmap (K L : D ⟶ E) (θ : K ⟹ L) :
  fmap[PostcomposeViaHcompose] θ ≈ fmap[Postcompose J] θ.
Proof.
  intro x; simpl.
  rewrite fmap_id; cat.
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition postcompose_via_hcompose_equiv :
  PostcomposeViaHcompose ≈ Postcompose J := (fun _ => iso_id; _).
Next Obligation.
  simpl; intros K L θ x.
  rewrite !fmap_id; cat.
Qed.

End ViaHcompose.

(** ** Mac Lane's own hypothesis: a full subcategory inclusion *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Theory.Concrete.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Finite.

Section FullSubcategory.

Context {C : Category}.
Context (S : Subcategory C).
Context (full : Subcategory.Full C S).
Context {D : Category}.

(* The two donors, by name: every subcategory inclusion is faithful, and a
   full one is a full functor. *)
Definition sub_Incl_Full : Category.Theory.Functor.Full (Incl C S) :=
  Full_Implies_Full_Functor C S full.

Definition sub_Incl_Faithful : Faithful (Incl C S) :=
  Incl_Faithful C S.

Definition SubPostcompose : [D, Sub C S] ⟶ [D, C] :=
  Postcompose (Incl C S).

Definition sub_postcompose_Faithful : Faithful SubPostcompose :=
  Postcompose_Faithful (Incl C S) sub_Incl_Faithful.

Definition sub_postcompose_Full :
  Category.Theory.Functor.Full SubPostcompose :=
  Postcompose_Full (Incl C S) sub_Incl_Full sub_Incl_Faithful.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sub_postcompose_hom_iso (K L : D ⟶ Sub C S) :
  (K ⟹ L) ≊ (Incl C S ◯ K ⟹ Incl C S ◯ L) :=
  postcompose_nat_bijection (Incl C S) sub_Incl_Full sub_Incl_Faithful K L.

End FullSubcategory.

Arguments SubPostcompose {C} S {D}.
Arguments sub_postcompose_hom_iso {C} S full {D} K L.

(** ** The concrete witness: finite setoids inside Sets *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FinSetsWitness.

#[local] Obligation Tactic := idtac.

Definition finpost_K : _1 ⟶ FinSetsCat := Diagonal _1 FinSets_bool.

Definition finpost_hom_iso :
  (finpost_K ⟹ finpost_K) ≊ (FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K) :=
  sub_postcompose_hom_iso FinSets FinSets_Full finpost_K finpost_K.

(* A non-identity transformation upstairs: negation of the two-element
   setoid, constant over the point. *)
Definition finpost_theta : finpost_K ⟹ finpost_K :=
  fmap[Diagonal _1] FinSets_negb.

Example finpost_theta_component (x : _1) :
  transform[finpost_theta] x = FinSets_negb := eq_refl.

(* A transformation exhibited DOWNSTAIRS, in [Sets], with no reference to
   the subcategory: its component is [Sets_negb].  Naturality over the point
   reduces to [Sets_negb ∘ fmap[J] id ≈ fmap[J] id ∘ Sets_negb]. *)
Program Definition finpost_phi :
  FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K := {|
  transform := fun _ => Sets_negb
|}.
Next Obligation. intros x y f; destruct f; simpl; cat. Qed.
Next Obligation. intros x y f; destruct f; simpl; cat. Qed.

Example finpost_phi_component (x : _1) :
  transform[finpost_phi] x = Sets_negb := eq_refl.

(*
   本节说明 Postcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma finpost_preimage_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x ≈ FinSets_negb.
Proof.
  exact (@fmap_sur _ _ _ (sub_Incl_Full FinSets FinSets_Full)
           _ _ (transform[finpost_phi] x)).
Qed.

(* Non-degeneracy, upstairs: the source Nat-setoid has at least two
   elements.  [FinSets_two_arrows] is Construction/Subcategory/Finite.v's
   separation of [id] from [FinSets_negb] in the subcategory's own
   hom-setoid. *)
Lemma finpost_theta_not_id : @nat_id _1 FinSetsCat finpost_K ≈ finpost_theta → False.
Proof.
  intro H.
  apply FinSets_two_arrows.
  exact (H ttt).
Qed.

(* Non-degeneracy, downstairs: so does the target Nat-setoid, and the
   witness is the image of [finpost_theta] under the isomorphism. *)
Lemma finpost_image_not_id :
  @nat_id _1 Sets (FinSets_Incl ◯ finpost_K) ≈ to finpost_hom_iso finpost_theta → False.
Proof.
  intro H.
  apply Sets_two_arrows.
  exact (H ttt).
Qed.

(* And the backward leg genuinely produces a non-identity: the preimage of
   [finpost_phi] is not the identity transformation. *)
Lemma finpost_preimage_not_id :
  @nat_id _1 FinSetsCat finpost_K ≈ from finpost_hom_iso finpost_phi → False.
Proof.
  intro H.
  apply FinSets_two_arrows.
  transitivity (transform[from finpost_hom_iso finpost_phi] ttt).
  - exact (H ttt).
  - exact (finpost_preimage_component ttt).
Qed.

(* The two exhibited transformations correspond under the isomorphism. *)
Lemma finpost_theta_phi : to finpost_hom_iso finpost_theta ≈ finpost_phi.
Proof. intro x; simpl; reflexivity. Qed.

End FinSetsWitness.

(** ** A boundary: fullness of J cannot be dropped *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FullnessNeeded.

#[local] Obligation Tactic := idtac.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition disc_obj (x : TwoDObj) : TwoObj :=
  match x with TwoDX => TwoX | TwoDY => TwoY end.

Definition disc_fmap {x y : TwoDObj} (f : TwoDHom x y) :
  TwoHom (disc_obj x) (disc_obj y) :=
  match f with TwoDIdX => TwoIdX | TwoDIdY => TwoIdY end.

Program Definition DiscToTwo : Two_Discrete ⟶ _2 := {|
  fobj := disc_obj;
  fmap := @disc_fmap
|}.
(* Two obligations only: [fmap_respects] is discharged by resolution, both
   hom-setoids here being [Morphism_equality], i.e. Leibniz. *)
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.
Next Obligation.
  intros x y z f g; destruct x, y, z;
    try (exact (False_rect _ (TwoDHom_X_Y_absurd f)));
    try (exact (False_rect _ (TwoDHom_X_Y_absurd g)));
    try (exact (False_rect _ (TwoDHom_Y_X_absurd f)));
    try (exact (False_rect _ (TwoDHom_Y_X_absurd g)));
    pose proof (TwoDHom_inv _ _ f) as Hf;
    pose proof (TwoDHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; reflexivity.
Qed.

(* Faithful: parallel arrows of the discrete category are equal, both being
   the unique identity constructor at their common endpoint, so the
   hypothesis is never even consulted. *)
Lemma DiscToTwo_Faithful : Faithful DiscToTwo.
Proof.
  constructor; intros x y f g Hfg; destruct x, y;
    try (exact (False_rect _ (TwoDHom_X_Y_absurd f)));
    try (exact (False_rect _ (TwoDHom_Y_X_absurd f)));
    pose proof (TwoDHom_inv _ _ f) as Hf;
    pose proof (TwoDHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; reflexivity.
Qed.

Lemma DiscToTwo_not_Full : Category.Theory.Functor.Full DiscToTwo → False.
Proof.
  intro HF.
  exact (TwoDHom_X_Y_absurd (@prefmap _ _ DiscToTwo HF TwoDX TwoDY TwoXY)).
Qed.

(* The two constant diagrams over the point. *)
Definition DiscX : _1 ⟶ Two_Discrete := @Diagonal Two_Discrete _1 TwoDX.
Definition DiscY : _1 ⟶ Two_Discrete := @Diagonal Two_Discrete _1 TwoDY.

(* Downstairs the arrow exists, so the target Nat-setoid is inhabited. *)
Program Definition disc_phi : DiscToTwo ◯ DiscX ⟹ DiscToTwo ◯ DiscY := {|
  transform := fun _ => TwoXY
|}.
Next Obligation. intros x y f; destruct f; reflexivity. Qed.
Next Obligation. intros x y f; destruct f; reflexivity. Qed.

(* Upstairs it does not, so [Postcompose DiscToTwo] is not full. *)
Theorem postcompose_full_needs_full :
  Category.Theory.Functor.Full (Postcompose (D:=_1) DiscToTwo) → False.
Proof.
  intro HF.
  exact (TwoDHom_X_Y_absurd
           (transform[@prefmap _ _ _ HF DiscX DiscY disc_phi] ttt)).
Qed.

(* Faithfulness, by contrast, does transfer: the postcomposition functor
   along the same J is faithful. *)
Definition postcompose_disc_Faithful : Faithful (Postcompose (D:=_1) DiscToTwo) :=
  Postcompose_Faithful DiscToTwo DiscToTwo_Faithful.

End FullnessNeeded.
