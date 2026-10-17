Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Kan's form of the coyoneda lemma over the category of elements. *)

(*
   nLab: https://ncatlab.org/nlab/show/category+of+elements

   本文件给出 Kan 扩张相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Kan.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(*
   本节说明 Kan 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation leg psi j :=
  (@vertex_map (Elements K) D _ (Elements_proj K) psi j).

Notation coh psi f :=
  (@cone_coherence (Elements K) D _ (Elements_proj K) psi _ _ f).

(** ** From a map into a representable to a cone *)

(*
   本节说明 Kan 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kan_cone_coherence {a : D} (tau : K ⟹ [Hom a,─])
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ transform[tau] (`1 x) (`2 x)
    ≈ transform[tau] (`1 y) (`2 y).
Proof.
  rewrite <- (`2 f).
  exact (naturality[tau] _ _ (`1 f) (`2 x)).
Qed.

Definition kan_cone_of_nat {a : D} (tau : K ⟹ [Hom a,─]) :
  ACone a (Elements_proj K) :=
  @Build_ACone (Elements K) D a (Elements_proj K)
    (fun j => transform[tau] (`1 j) (`2 j))
    (fun x y f => kan_cone_coherence tau f).

(* The leg at a pair is the component of τ evaluated at the element, on
   the nose. *)
Example kan_cone_of_nat_leg {a : D} (tau : K ⟹ [Hom a,─])
        (d : D) (x : K d) :
  leg (kan_cone_of_nat tau) ((d; x) : Elements K) = transform[tau] d x
  := eq_refl.

(** ** From a cone to a map into a representable *)

(*
   本节说明 Kan 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma elements_same_cond {d : D} (x y : K d) (H : x ≈ y) :
  fmap[K] (id[d]) x ≈ y.
Proof. now rewrite (elements_id_cond K x). Qed.

Definition elements_same {d : D} (x y : K d) (H : x ≈ y) :
  ((d; x) : Elements K) ~{Elements K}~> (d; y) :=
  (id[d]; elements_same_cond x y H).

(* Respectfulness of a cone's leg family in the ELEMENT argument, derived
   from cone coherence at [elements_same] rather than assumed. *)

Lemma kan_leg_respects {a : D} (psi : ACone a (Elements_proj K))
      {d : D} (x y : K d) (H : x ≈ y) :
  leg psi ((d; x) : Elements K) ≈ leg psi ((d; y) : Elements K).
Proof.
  pose proof (coh psi (elements_same x y H)) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  now rewrite id_left.
Qed.

(*
   本节说明 Kan 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kan_nat_naturality {a : D} (psi : ACone a (Elements_proj K))
      {d d' : D} (f : d ~> d') (x : K d) :
  f ∘ leg psi ((d; x) : Elements K)
    ≈ leg psi ((d'; fmap[K] f x) : Elements K).
Proof. exact (coh psi (Elements_lift K x f)). Qed.

Lemma kan_nat_naturality_sym {a : D} (psi : ACone a (Elements_proj K))
      {d d' : D} (f : d ~> d') (x : K d) :
  leg psi ((d'; fmap[K] f x) : Elements K)
    ≈ f ∘ leg psi ((d; x) : Elements K).
Proof. symmetry; exact (coh psi (Elements_lift K x f)). Qed.

Definition kan_nat_of_cone {a : D} (psi : ACone a (Elements_proj K)) :
  K ⟹ [Hom a,─] :=
  @Build_Transform D Sets K ([Hom a,─])
    (fun d => @Build_SetoidMorphism (K d) _ (@hom D a d) _
                (fun x => leg psi ((d; x) : Elements K))
                (fun x y H => kan_leg_respects psi x y H))
    (fun d d' f => kan_nat_naturality psi f)
    (fun d d' f => kan_nat_naturality_sym psi f).

(* The component at d, evaluated at an element, is the leg at the pair,
   on the nose. *)
Example kan_nat_of_cone_component {a : D} (psi : ACone a (Elements_proj K))
        (d : D) (x : K d) :
  transform[kan_nat_of_cone psi] d x = leg psi ((d; x) : Elements K)
  := eq_refl.

(** ** The two round trips *)

(* Both hold at `≈` and neither holds at [eq_refl]; the negatives are
   pinned in Test/ProbeCoyoneda.v.  The cone side must destruct the pair
   first, stdlib [sigT] having no eta rule here. *)

Lemma kan_nat_cone_nat {a : D} (tau : K ⟹ [Hom a,─]) :
  kan_nat_of_cone (kan_cone_of_nat tau) ≈ tau.
Proof. intros d x; reflexivity. Qed.

Lemma kan_cone_nat_cone {a : D} (psi : ACone a (Elements_proj K)) :
  @equiv _ (AConeEquiv a (Elements_proj K))
         (kan_cone_of_nat (kan_nat_of_cone psi)) psi.
Proof. intros [d x]; reflexivity. Qed.

(** ** The two sides as functors of the apex *)

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition KanNat : D^op ⟶ Sets :=
  Curried_Hom ([D, Sets]) K ◯ Curried_Hom D.

(* The right-hand side is Structure/Cone.v's presheaf of cones, taken at
   the elements projection.  Also pure reuse. *)

Definition KanCone : D^op ⟶ Sets :=
  ConePresheaf (Elements_proj K).

(* Both object actions are the setoids the exercise names, on the nose. *)

Example kan_nat_obj (a : D) :
  KanNat a = {| carrier   := K ~{[D, Sets]}~> [Hom a,─]
              ; is_setoid := @homset ([D, Sets]) K [Hom a,─] |}
  := eq_refl.

Example kan_cone_obj (a : D) :
  KanCone a = {| carrier   := ACone a (Elements_proj K)
               ; is_setoid := AConeEquiv a (Elements_proj K) |}
  := eq_refl.

(** ** The pointwise isomorphism *)

Program Definition kan_iso_at (a : D) : KanNat a ≅[Sets] KanCone a := {|
  to   := {| morphism := fun tau => kan_cone_of_nat tau |};
  from := {| morphism := fun psi => kan_nat_of_cone psi |}
|}.
Next Obligation. intros a tau tau' H [d z]; exact (H d z). Qed.
Next Obligation. intros a psi psi' H d z; exact (H (d; z)). Qed.
Next Obligation. intros a psi; apply kan_cone_nat_cone. Qed.
Next Obligation. intros a tau; apply kan_nat_cone_nat. Qed.

(** ** Naturality in the apex *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition kan_coyoneda : KanNat ≅[[D^op, Sets]] KanCone := {|
  to   := {| transform := fun a => to   (kan_iso_at a) |};
  from := {| transform := fun a => from (kan_iso_at a) |}
|}.
Next Obligation. intros a a' g tau [d z]; reflexivity. Qed.
Next Obligation. intros a a' g tau [d z]; reflexivity. Qed.
Next Obligation. intros a a' g psi d z; reflexivity. Qed.
Next Obligation. intros a a' g psi d z; reflexivity. Qed.
Next Obligation. intros a psi [d z]; simpl; now rewrite id_right. Qed.
Next Obligation. intros a tau d z; simpl; now rewrite id_right. Qed.

(* The upgrade is an upgrade: the components ARE the pointwise legs. *)

Example kan_coyoneda_to_component (a : D) :
  transform[to kan_coyoneda] a = to (kan_iso_at a) := eq_refl.

Example kan_coyoneda_from_component (a : D) :
  transform[from kan_coyoneda] a = from (kan_iso_at a) := eq_refl.

(** ** The literal Δ-reading *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kan_transform_naturality {a : D} (psi : ACone a (Elements_proj K))
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ leg psi x
    ≈ leg psi y ∘ fmap[Δ[Elements K](a)] f.
Proof. rewrite id_right; exact (coh psi f). Qed.

Lemma kan_transform_naturality_sym {a : D} (psi : ACone a (Elements_proj K))
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  leg psi y ∘ fmap[Δ[Elements K](a)] f
    ≈ fmap[Elements_proj K] f ∘ leg psi x.
Proof. rewrite id_right; symmetry; exact (coh psi f). Qed.

Definition kan_transform_of_cone {a : D}
           (psi : ACone a (Elements_proj K)) :
  Δ[Elements K](a) ⟹ Elements_proj K :=
  @Build_Transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K)
    (fun j => leg psi j)
    (fun x y f => kan_transform_naturality psi f)
    (fun x y f => kan_transform_naturality_sym psi f).

Lemma kan_cone_of_transform_coherence {a : D}
      (theta : Δ[Elements K](a) ⟹ Elements_proj K)
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ transform[theta] x ≈ transform[theta] y.
Proof.
  rewrite <- (id_right (transform[theta] y)).
  exact (naturality[theta] _ _ f).
Qed.

Definition kan_cone_of_transform {a : D}
           (theta : Δ[Elements K](a) ⟹ Elements_proj K) :
  ACone a (Elements_proj K) :=
  @Build_ACone (Elements K) D a (Elements_proj K)
    (fun j => transform[theta] j)
    (fun x y f => kan_cone_of_transform_coherence theta f).

Example kan_transform_of_cone_component {a : D}
        (psi : ACone a (Elements_proj K)) (j : Elements K) :
  transform[kan_transform_of_cone psi] j = leg psi j := eq_refl.

Example kan_cone_of_transform_leg {a : D}
        (theta : Δ[Elements K](a) ⟹ Elements_proj K) (j : Elements K) :
  leg (kan_cone_of_transform theta) j = transform[theta] j := eq_refl.

Lemma kan_cone_transform_cone {a : D} (psi : ACone a (Elements_proj K)) :
  @equiv _ (AConeEquiv a (Elements_proj K))
         (kan_cone_of_transform (kan_transform_of_cone psi)) psi.
Proof. intro j; reflexivity. Qed.

Lemma kan_transform_cone_transform {a : D}
      (theta : Δ[Elements K](a) ⟹ Elements_proj K) :
  kan_transform_of_cone (kan_cone_of_transform theta) ≈ theta.
Proof. intro j; reflexivity. Qed.

(* The setoid of Δ-transformations, named so the two isomorphisms below
   can mention it without repeating the packaging. *)

Definition KanDelta (a : D) : SetoidObject :=
  {| carrier   := Δ[Elements K](a) ~{[Elements K, D]}~> Elements_proj K
   ; is_setoid := @homset ([Elements K, D])
                          Δ[Elements K](a) (Elements_proj K) |}.

Program Definition kan_cone_transform_iso (a : D) :
  KanCone a ≅[Sets] KanDelta a := {|
  to   := {| morphism := fun psi   => kan_transform_of_cone psi |};
  from := {| morphism := fun theta => kan_cone_of_transform theta |}
|}.
Next Obligation. intros a psi psi' H j; exact (H j). Qed.
Next Obligation. intros a th th' H j; exact (H j). Qed.
Next Obligation. intros a th; apply kan_transform_cone_transform. Qed.
Next Obligation. intros a psi; apply kan_cone_transform_cone. Qed.

(* Mac Lane's own phrasing: Nat(K, D(a,−)) ≅ Nat(Δa, Q). *)

Definition kan_iso_transform (a : D) : KanNat a ≅[Sets] KanDelta a :=
  iso_compose (kan_cone_transform_iso a) (kan_iso_at a).

End Kan.
