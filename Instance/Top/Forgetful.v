Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Top.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/adjoint+triple

   本文件给出遗忘函子相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** The underlying-set functor *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Top_Forget@{o h so | o < h, h < so +} :
  Top@{h o} ⟶ Sets@{h so} := {|
  fobj := fun X : TopSpace@{o} => Setoid_Lift@{o h} (top_carrier X);
  fmap := fun X Y f => SetoidMorphism_Lift@{o h} (continuous_map f)
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Top_Forget_Faithful : Faithful Top_Forget.
Proof. constructor; intros x y f g H p; exact (H p). Qed.

(** ** The discrete-topology functor and its transposition *)

Program Definition Top_Discrete@{o h so | o < h, o < so +} :
  Sets@{o so} ⟶ Top@{h o} := {|
  fobj := fun A : SetoidObject@{o o} => Discrete_Top@{o o} A;
  fmap := fun A B f => {|
    continuous_map := f;
    continuity := out_of_discrete_continuous A (Discrete_Top B) f
  |}
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition discrete_adj (A : SetoidObject) (Y : TopSpace) :
  @Isomorphism Sets
    {| carrier := Top_Discrete A ~{Top}~> Y
     ; is_setoid := @homset Top (Top_Discrete A) Y |}
    (Setoid_Lift
       {| carrier := A ~{Sets}~> top_carrier Y
        ; is_setoid := @homset Sets A (top_carrier Y) |}) := {|
  to := {| morphism := fun f => continuous_map f |};
  from := {| morphism := fun g =>
    {| continuous_map := g;
       continuity := out_of_discrete_continuous A Y g |} |}
|}.
Next Obligation. intros A Y f g H; exact H. Qed.
Next Obligation. intros A Y f g H; exact H. Qed.
Next Obligation. intros A Y g p; reflexivity. Qed.
Next Obligation. intros A Y f p; reflexivity. Qed.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma discrete_adj_nat_l (A A' : SetoidObject) (Y : TopSpace)
  (f : Top_Discrete A ~{Top}~> Y) (g : A' ~{Sets}~> A) :
  to (discrete_adj A' Y) (f ∘[Top] fmap[Top_Discrete] g)
    ≈ to (discrete_adj A Y) f ∘[Sets] g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_nat_r (A : SetoidObject) (Y Z : TopSpace)
  (f : Y ~{Top}~> Z) (g : Top_Discrete A ~{Top}~> Y) :
  to (discrete_adj A Z) (f ∘[Top] g)
    ≈ continuous_map f ∘[Sets] to (discrete_adj A Y) g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_inv_nat_l (A A' : SetoidObject) (Y : TopSpace)
  (f : A ~{Sets}~> top_carrier Y) (g : A' ~{Sets}~> A) :
  from (discrete_adj A' Y) (f ∘[Sets] g)
    ≈ from (discrete_adj A Y) f ∘[Top] fmap[Top_Discrete] g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_inv_nat_r (A : SetoidObject) (Y Z : TopSpace)
  (f : Y ~{Top}~> Z) (g : A ~{Sets}~> top_carrier Y) :
  from (discrete_adj A Z) (continuous_map f ∘[Sets] g)
    ≈ f ∘[Top] from (discrete_adj A Y) g.
Proof. intro p; reflexivity. Qed.

(** ** The indiscrete-topology functor and its transposition *)

Program Definition Top_Indiscrete@{o h so | o < h, o < so +} :
  Sets@{o so} ⟶ Top@{h o} := {|
  fobj := fun A : SetoidObject@{o o} => Indiscrete_Top@{o o} A;
  fmap := fun A B f => {|
    continuous_map := f;
    continuity := into_indiscrete_continuous (Indiscrete_Top A) B f
  |}
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition indiscrete_adj (X : TopSpace) (B : SetoidObject) :
  @Isomorphism Sets
    (Setoid_Lift
       {| carrier := top_carrier X ~{Sets}~> B
        ; is_setoid := @homset Sets (top_carrier X) B |})
    {| carrier := X ~{Top}~> Top_Indiscrete B
     ; is_setoid := @homset Top X (Top_Indiscrete B) |} := {|
  to := {| morphism := fun g =>
    {| continuous_map := g;
       continuity := into_indiscrete_continuous X B g |} |};
  from := {| morphism := fun f => continuous_map f |}
|}.
Next Obligation. intros X B f g H; exact H. Qed.
Next Obligation. intros X B f g H; exact H. Qed.
Next Obligation. intros X B f p; reflexivity. Qed.
Next Obligation. intros X B g p; reflexivity. Qed.

Lemma indiscrete_adj_nat_l (X X' : TopSpace) (B : SetoidObject)
  (g : top_carrier X ~{Sets}~> B) (f : X' ~{Top}~> X) :
  to (indiscrete_adj X' B) (g ∘[Sets] continuous_map f)
    ≈ to (indiscrete_adj X B) g ∘[Top] f.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_nat_r (X : TopSpace) (B B' : SetoidObject)
  (g' : B ~{Sets}~> B') (g : top_carrier X ~{Sets}~> B) :
  to (indiscrete_adj X B') (g' ∘[Sets] g)
    ≈ fmap[Top_Indiscrete] g' ∘[Top] to (indiscrete_adj X B) g.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_inv_nat_l (X X' : TopSpace) (B : SetoidObject)
  (f : X ~{Top}~> Top_Indiscrete B) (g : X' ~{Top}~> X) :
  from (indiscrete_adj X' B) (f ∘[Top] g)
    ≈ from (indiscrete_adj X B) f ∘[Sets] continuous_map g.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_inv_nat_r (X : TopSpace) (B B' : SetoidObject)
  (g' : B ~{Sets}~> B') (f : X ~{Top}~> Top_Indiscrete B) :
  from (indiscrete_adj X B') (fmap[Top_Indiscrete] g' ∘[Top] f)
    ≈ g' ∘[Sets] from (indiscrete_adj X B) f.
Proof. intro p; reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition discrete_forget_indiscrete_triple :=
  (@discrete_adj, @indiscrete_adj,
   (@discrete_adj_nat_l, @discrete_adj_nat_r,
    @discrete_adj_inv_nat_l, @discrete_adj_inv_nat_r),
   (@indiscrete_adj_nat_l, @indiscrete_adj_nat_r,
    @indiscrete_adj_inv_nat_l, @indiscrete_adj_inv_nat_r)).

(*
   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Forget_Diagram {J : Category} (K : J ⟶ Top) :
  J ⟶ Sets := {|
  fobj := fun j => top_carrier (K j);
  fmap := fun i j f => continuous_map (fmap[K] f)
|}.
Next Obligation.
  intros J K i j f g H p.
  exact (@fmap_respects _ _ K i j f g H p).
Qed.
Next Obligation. intros J K j p; exact (@fmap_id _ _ K j p). Qed.
Next Obligation.
  intros J K i j k f g p; exact (@fmap_comp _ _ K i j k f g p).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Forget_preserves_limit_cone {J : Category} {K : J ⟶ Top}
  (N : Cone K) (HN : IsLimitCone N)
  (A : SetoidObject) (legs : ∀ j : J, A ~{Sets}~> top_carrier (K j))
  (coh : ∀ (x y : J) (f : x ~{J}~> y),
     continuous_map (fmap[K] f) ∘[Sets] legs x ≈ legs y) :
  ∃! u : A ~{Sets}~> top_carrier (vertex_obj[N]),
    ∀ j : J, continuous_map (cone_leg N j) ∘[Sets] u ≈ legs j.
Proof.
  pose (M' := @Build_Cone J Top K (Discrete_Top A)
    (@Build_ACone J Top (Discrete_Top A) K
       (fun j => Build_ContinuousMorphism (Discrete_Top A) (K j)
                   (legs j)
                   (out_of_discrete_continuous A (K j) (legs j)))
       (fun x y f => coh x y f))).
  destruct (HN M') as [u Hu Huniq].
  unshelve refine {| unique_obj := continuous_map u |}.
  - intros j p; exact (Hu j p).
  - intros v Hv p.
    exact (Huniq (Build_ContinuousMorphism (Discrete_Top A)
                    (vertex_obj[N]) v
                    (out_of_discrete_continuous A (vertex_obj[N]) v))
                 (fun j q => Hv j q) p).
Defined.

(* Stripping preserves colimiting cocones, dually: a raw Sets-side
   cocone competitor transposes along the indiscrete topology.  LAPC for
   Forget ⊣ Indiscrete. *)
Theorem Forget_preserves_colimit_cocone {J : Category} {K : J ⟶ Top}
  (N : Cocone K) (HN : IsColimitCocone N)
  (A : SetoidObject) (injs : ∀ j : J, top_carrier (K j) ~{Sets}~> A)
  (coh : ∀ (x y : J) (f : x ~{J}~> y),
     injs y ∘[Sets] continuous_map (fmap[K] f) ≈ injs x) :
  ∃! u : top_carrier (vertex_obj[N]) ~{Sets}~> A,
    ∀ j : J, u ∘[Sets] continuous_map (cocone_inj N j) ≈ injs j.
Proof.
  pose (M' := @Build_Cone (J^op) (Top^op) (K^op) (Indiscrete_Top A)
    (@Build_ACone (J^op) (Top^op) (Indiscrete_Top A) (K^op)
       (fun j => Build_ContinuousMorphism (K j) (Indiscrete_Top A)
                   (injs j)
                   (into_indiscrete_continuous (K j) A (injs j)))
       (fun x y f => coh y x f))).
  destruct (HN M') as [u Hu Huniq].
  unshelve refine {| unique_obj := continuous_map u |}.
  - intros j p; exact (Hu j p).
  - intros v Hv p.
    exact (Huniq (Build_ContinuousMorphism (vertex_obj[N])
                    (Indiscrete_Top A) v
                    (into_indiscrete_continuous (vertex_obj[N]) A v))
                 (fun j q => Hv j q) p).
Defined.

(** ** Exercise 2: the indiscrete functor has no right adjoint *)

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Coherence of a cocone over a discrete shape, in any category: the only
   arrows are (transported) identities. *)
Lemma discrete_cocone_coherence {A : Type} {C : Category}
  (H : DiscreteCat A ⟶ C) (c : C) (inj : ∀ x : A, H x ~{C}~> c)
  {x y : A} (f : y ~{DiscreteCat A}~> x) :
  inj x ∘ fmap[H] f ≈ inj y.
Proof.
  destruct f.
  change (inj y ∘ fmap[H] (@id (DiscreteCat A) y) ≈ inj y).
  rewrite fmap_id; apply id_right.
Qed.

(* The discrete pair of one-point setoids. *)
Definition unit_pair_diagram : DiscreteCat bool ⟶ Sets :=
  @DiscreteCat_Functor bool Sets (fun _ => unit_setoid_object).

(* The coproduct cocone: apex the two-point setoid, injections the two
   constants. *)
Definition bool_cocone : Cocone unit_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Sets^op) (unit_pair_diagram^op)
    bool_setoid_object
    (@Build_ACone ((DiscreteCat bool)^op) (Sets^op) bool_setoid_object
       (unit_pair_diagram^op)
       (fun b => const_morphism unit_setoid_object bool_setoid_object b)
       (fun x y f => discrete_cocone_coherence unit_pair_diagram
                       bool_setoid_object _ f)).

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bool_cocone_colimit : IsColimitCocone bool_cocone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := {| morphism := fun b : bool =>
         if b then cocone_inj M true ttt else cocone_inj M false ttt |} |}.
  - intros x; destruct x; intro p; destruct p; simpl; reflexivity.
  - intros v Hv b; destruct b.
    + symmetry; exact (Hv true ttt).
    + symmetry; exact (Hv false ttt).
Defined.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition indiscrete_pair_diagram@{o h so | o < h, o < so +} :
  DiscreteCat@{h h h} bool ⟶ Top@{h o} := {|
  fobj := fun _ : bool => Indiscrete_Top@{o o} unit_setoid_object@{o o};
  fmap := fun _ _ _ => top_id
|}.
Next Obligation. intros x y f g H p; reflexivity. Qed.
Next Obligation. intros x p; reflexivity. Qed.
Next Obligation. intros x y z f g p; reflexivity. Qed.

(* The indiscrete image of the coproduct cocone: apex the two-point
   indiscrete space, injections the images of the two constants. *)
Definition indiscrete_image_cocone : Cocone indiscrete_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Top^op) (indiscrete_pair_diagram^op)
    TwoPoint_Indiscrete
    (@Build_ACone ((DiscreteCat bool)^op) (Top^op) TwoPoint_Indiscrete
       (indiscrete_pair_diagram^op)
       (fun b => fmap[Top_Indiscrete]
                   (const_morphism unit_setoid_object bool_setoid_object b))
       (fun x y f => discrete_cocone_coherence indiscrete_pair_diagram
                       TwoPoint_Indiscrete _ f)).

(*
   本节说明 Forgetful 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition disc_leg (b : bool) :
  Indiscrete_Top unit_setoid_object ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism (Indiscrete_Top unit_setoid_object) Bool_Discrete
    (const_morphism unit_setoid_object bool_setoid_object b)
    (fun U _ => open_const (Indiscrete_Top unit_setoid_object) (U b)).

Definition disc_cocone : Cocone indiscrete_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Top^op) (indiscrete_pair_diagram^op)
    Bool_Discrete
    (@Build_ACone ((DiscreteCat bool)^op) (Top^op) Bool_Discrete
       (indiscrete_pair_diagram^op)
       (fun b => disc_leg b)
       (fun x y f => discrete_cocone_coherence indiscrete_pair_diagram
                       Bool_Discrete _ f)).

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem indiscrete_image_not_colimiting :
  IsColimitCocone indiscrete_image_cocone → False.
Proof.
  intro P.
  pose proof (colimitcocone_ump P disc_cocone) as U.
  pose proof (unique_property U true ttt) as Ht.
  pose proof (unique_property U false ttt) as Hf.
  simpl in Ht, Hf.
  pose proof (continuity (unique_obj U)
                (fun b : bool_setoid_object => b = true)
                singleton_true_open true false) as HO.
  discriminate (eq_trans (eq_sym Hf) (HO Ht)).
Qed.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem indiscrete_no_right_adjoint
  (R₀ : TopSpace → SetoidObject)
  (φ : ∀ (A : SetoidObject) (Y : TopSpace),
     @Isomorphism Sets
       {| carrier := Top_Indiscrete A ~{Top}~> Y
        ; is_setoid := @homset Top (Top_Indiscrete A) Y |}
       (Setoid_Lift
          {| carrier := A ~{Sets}~> R₀ Y
           ; is_setoid := @homset Sets A (R₀ Y) |}))
  (φ_nat : ∀ (A A' : SetoidObject) (g : A' ~{Sets}~> A) (Y : TopSpace)
             (f : Top_Indiscrete A ~{Top}~> Y),
     to (φ A' Y) (f ∘[Top] fmap[Top_Indiscrete] g)
       ≈ to (φ A Y) f ∘[Sets] g) :
  False.
Proof.
  (* the transposed legs, as points of R₀ Bool_Discrete *)
  pose (r := fun b : bool =>
               to (φ unit_setoid_object Bool_Discrete) (disc_leg b) ttt).
  (* the induced map out of the coproduct, and its transpose back *)
  assert (sp : Proper (respectful (@equiv _ (is_setoid bool_setoid_object))
                                  (@equiv _ (is_setoid (R₀ Bool_Discrete))))
                 (fun b : bool => if b then r true else r false)).
  { intros b b' Hb; simpl in Hb; subst; reflexivity. }
  pose (s := {| morphism := fun b : bool => if b then r true else r false
              ; proper_morphism := sp |}
             : bool_setoid_object ~{Sets}~> R₀ Bool_Discrete).
  pose (h := from (φ bool_setoid_object Bool_Discrete) s).
  (* h restricts along each injection to the corresponding leg: transpose,
     compute through the bijection's round trips, transpose back *)
  assert (Hleg : ∀ b : bool,
    h ∘[Top] fmap[Top_Indiscrete]
        (const_morphism unit_setoid_object bool_setoid_object b)
      ≈ disc_leg b).
  { intro b.
    assert (E : to (φ unit_setoid_object Bool_Discrete)
                   (h ∘[Top] fmap[Top_Indiscrete]
                      (const_morphism unit_setoid_object
                         bool_setoid_object b))
                  ≈ to (φ unit_setoid_object Bool_Discrete) (disc_leg b)).
    { etransitivity.
      { exact (φ_nat _ _ (const_morphism unit_setoid_object
                            bool_setoid_object b) _ h). }
      intro p; destruct p, b; simpl.
      - exact (iso_to_from (φ bool_setoid_object Bool_Discrete) s true).
      - exact (iso_to_from (φ bool_setoid_object Bool_Discrete) s false).
    }
    transitivity (from (φ unit_setoid_object Bool_Discrete)
                    (to (φ unit_setoid_object Bool_Discrete)
                        (h ∘[Top] fmap[Top_Indiscrete]
                           (const_morphism unit_setoid_object
                              bool_setoid_object b)))).
    { symmetry.
      exact (iso_from_to (φ unit_setoid_object Bool_Discrete) _). }
    transitivity (from (φ unit_setoid_object Bool_Discrete)
                    (to (φ unit_setoid_object Bool_Discrete) (disc_leg b))).
    { exact (proper_morphism (from (φ unit_setoid_object Bool_Discrete))
               _ _ E). }
    exact (iso_from_to (φ unit_setoid_object Bool_Discrete) (disc_leg b)).
  }
  (* whence h true = true and h false = false; continuity is refuted *)
  pose proof (Hleg true ttt) as Ht; simpl in Ht.
  pose proof (Hleg false ttt) as Hf; simpl in Hf.
  pose proof (continuity h (fun b : bool_setoid_object => b = true)
                singleton_true_open true false) as HO.
  discriminate (eq_trans (eq_sym Hf) (HO Ht)).
Qed.

(** ** Acceptance tests

    The definitional facts the header claims really are definitional. *)

(* Both adjoints are sections of the forgetful functor on objects, on the
   nose: forgetting either extreme topology returns the very lift of the
   original setoid. *)
Example forget_discrete_on_objects (A : SetoidObject) :
  Top_Forget (Top_Discrete A) = Setoid_Lift A := eq_refl.
Example forget_indiscrete_on_objects (A : SetoidObject) :
  Top_Forget (Top_Indiscrete A) = Setoid_Lift A := eq_refl.

(* Both transposition bijections are the identity on underlying maps. *)
Example discrete_transpose_identity (A : SetoidObject) (Y : TopSpace)
  (f : Top_Discrete A ~{Top}~> Y) :
  to (discrete_adj A Y) f = continuous_map f := eq_refl.
Example indiscrete_transpose_identity (X : TopSpace) (B : SetoidObject)
  (f : X ~{Top}~> Top_Indiscrete B) :
  from (indiscrete_adj X B) f = continuous_map f := eq_refl.

(* The indiscrete image of the coproduct apex is exactly the two-point
   indiscrete probe space of Instance/Top.v. *)
Example image_apex_is_TwoPoint_Indiscrete :
  vertex_obj[indiscrete_image_cocone] = TwoPoint_Indiscrete := eq_refl.
Example image_apex_is_indiscrete_of_bool :
  vertex_obj[indiscrete_image_cocone]
    = Top_Indiscrete (vertex_obj[bool_cocone]) := eq_refl.
