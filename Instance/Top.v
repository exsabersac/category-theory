Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * The category of topological spaces *)

(*
 nLab:      https://ncatlab.org/nlab/show/Top
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_topological_spaces
 Book:      Fong and Spivak, "Seven Sketches in Compositionality",
 Book:      Riehl, "Category Theory in Context", Examples 1.3.14(iv)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:      https://ncatlab.org/nlab/show/locale
   nLab:      https://ncatlab.org/nlab/show/constructive+mathematics
   Book:      Johnstone, "Stone Spaces", CUP 1982 (the locale/space
   Book:      Bishop, "Foundations of Constructive Analysis", McGraw-Hill

   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Spaces *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record TopSpace@{o} := {
  top_carrier :> SetoidObject@{o o};    (* the setoid of points *)

  (* the topology: which predicates on the points are open *)
  IsOpen : (top_carrier → Type@{o}) → Type@{o};

  (* being open is invariant under pointwise equivalence of predicates *)
  open_respects (U V : top_carrier → Type@{o}) :
    (∀ x, U x ↔ V x) → IsOpen U → IsOpen V;

  (* every open respects the carrier's own equality on points *)
  open_proper (U : top_carrier → Type@{o}) :
    IsOpen U → ∀ x y : top_carrier, x ≈ y → U x → U y;

  (* closure under arbitrary (type-indexed) unions *)
  open_union (I : Type@{o}) (U : I → (top_carrier → Type@{o})) :
    (∀ i, IsOpen (U i)) → IsOpen (fun x => { i : I & U i x });

  (* the whole space is open *)
  open_whole : IsOpen (fun _ => poly_unit@{o});

  (* closure under binary intersection *)
  open_inter (U V : top_carrier → Type@{o}) :
    IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma open_const (X : TopSpace) (P : Type) : IsOpen X (fun _ => P).
Proof.
  apply (open_respects X (fun _ => { _ : P & poly_unit }) (fun _ => P)).
  - intro x; split.
    + exact (fun w => projT1 w).
    + exact (fun p => (p; ttt)).
  - apply (open_union X P (fun _ _ => poly_unit)).
    intro i; exact (open_whole X).
Qed.

(* The empty predicate is open: the union over the empty index type, which
   is the [P := False] case of [open_const]. *)
Corollary open_empty (X : TopSpace) : IsOpen X (fun _ => False).
Proof. exact (open_const X False). Qed.

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma open_uniform (X : TopSpace) (U : X → Type) :
  (∀ x y : X, U x → U y) → IsOpen X U.
Proof.
  intro HU.
  apply (open_respects X (fun _ => { z : X & U z }) U).
  - intro x; split.
    + intro w; exact (HU (projT1 w) x (projT2 w)).
    + intro Ux; exact (x; Ux).
  - apply open_const.
Qed.

(** ** Continuous maps *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Continuous (X Y : TopSpace)
           (f : SetoidMorphism (top_carrier X) (top_carrier Y)) : Type :=
  ∀ U : Y → Type, IsOpen Y U → IsOpen X (fun x => U (f x)).

(* A morphism of [Top]: a setoid map on points that is moreover continuous.
   This wraps [SetoidMorphism] exactly as [SetoidMorphism] wraps a bare
   function in Instance/Sets.v. *)
Record ContinuousMorphism (X Y : TopSpace) := {
  continuous_map :> SetoidMorphism (top_carrier X) (top_carrier Y);
  continuity : Continuous X Y continuous_map
}.

Arguments continuous_map {X Y} _.
Arguments continuity {X Y} _ _ _.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ContinuousMorphism_equiv@{o h p | o < h, h <= p +}
  {X Y : TopSpace@{o}} : crelation@{h p} (ContinuousMorphism@{h o} X Y) :=
  fun f g => ∀ x : X, continuous_map f x ≈ continuous_map g x.

Arguments ContinuousMorphism_equiv {X Y} _ _ /.

#[export]
Program Instance ContinuousMorphism_Setoid@{o h p | o < h, h <= p +}
  {X Y : TopSpace@{o}} : Setoid@{h p} (ContinuousMorphism@{h o} X Y) := {|
  equiv := ContinuousMorphism_equiv@{o h p}
|}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (continuous_map g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

(* The identity map is continuous: the preimage of U along the identity is
   U itself, up to eta. *)
Definition top_id {X : TopSpace} : ContinuousMorphism X X := {|
  continuous_map := setoid_morphism_id;
  continuity := fun _ H => H
|}.

(* Composition: preimages compose contravariantly, so the preimage along
   `g ∘ f` of an open is the preimage along `f` of the preimage along `g`. *)
Definition top_compose {X Y Z : TopSpace}
           (g : ContinuousMorphism Y Z) (f : ContinuousMorphism X Y) :
  ContinuousMorphism X Z := {|
  continuous_map := setoid_morphism_compose g f;
  continuity := fun U H => continuity f _ (continuity g U H)
|}.

Lemma top_compose_respects {X Y Z : TopSpace} :
  Proper (equiv ==> equiv ==> equiv) (@top_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (continuous_map f1 x)).
  apply proper_morphism, Hf.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Top : Category := {|
  obj     := TopSpace;
  hom     := ContinuousMorphism;
  homset  := @ContinuousMorphism_Setoid;
  id      := @top_id;
  compose := @top_compose;

  compose_respects := @top_compose_respects
|}.

(** ** Two extreme topologies *)

Section Discrete.

Context (A : SetoidObject).

(* The discrete topology: EVERY predicate that respects the carrier's `≈`
   is open.  Setoid bookkeeping is the only constraint left; this is the
   finest topology on A. *)
Definition discrete_open (U : A → Type) : Type :=
  ∀ x y : A, x ≈ y → U x → U y.

Lemma discrete_respects (U V : A → Type) :
  (∀ x, U x ↔ V x) → discrete_open U → discrete_open V.
Proof.
  intros HUV HU x y Hxy Vx.
  exact (fst (HUV y) (HU x y Hxy (snd (HUV x) Vx))).
Qed.

Lemma discrete_union (I : Type) (U : I → (A → Type)) :
  (∀ i, discrete_open (U i)) → discrete_open (fun x => { i : I & U i x }).
Proof.
  intros HU x y Hxy w.
  exact (projT1 w; HU (projT1 w) x y Hxy (projT2 w)).
Qed.

Lemma discrete_whole : discrete_open (fun _ => poly_unit).
Proof. intros x y Hxy w; exact w. Qed.

Lemma discrete_inter (U V : A → Type) :
  discrete_open U → discrete_open V → discrete_open (fun x => U x ∧ V x).
Proof.
  intros HU HV x y Hxy w.
  exact (HU x y Hxy (fst w), HV x y Hxy (snd w)).
Qed.

Definition Discrete_Top : TopSpace := {|
  top_carrier    := A;
  IsOpen         := discrete_open;
  open_respects  := discrete_respects;
  open_proper    := fun _ H => H;
  open_union     := discrete_union;
  open_whole     := discrete_whole;
  open_inter     := discrete_inter
|}.

End Discrete.

Section Indiscrete.

Context (A : SetoidObject).

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition indiscrete_open (U : A → Type) : Type :=
  ∀ x y : A, U x → U y.

Lemma indiscrete_respects (U V : A → Type) :
  (∀ x, U x ↔ V x) → indiscrete_open U → indiscrete_open V.
Proof.
  intros HUV HU x y Vx.
  exact (fst (HUV y) (HU x y (snd (HUV x) Vx))).
Qed.

Lemma indiscrete_proper (U : A → Type) :
  indiscrete_open U → ∀ x y : A, x ≈ y → U x → U y.
Proof. intros HU x y _ Ux; exact (HU x y Ux). Qed.

Lemma indiscrete_union (I : Type) (U : I → (A → Type)) :
  (∀ i, indiscrete_open (U i)) → indiscrete_open (fun x => { i : I & U i x }).
Proof.
  intros HU x y w.
  exact (projT1 w; HU (projT1 w) x y (projT2 w)).
Qed.

Lemma indiscrete_whole : indiscrete_open (fun _ => poly_unit).
Proof. intros x y w; exact w. Qed.

Lemma indiscrete_inter (U V : A → Type) :
  indiscrete_open U → indiscrete_open V →
  indiscrete_open (fun x => U x ∧ V x).
Proof.
  intros HU HV x y w.
  exact (HU x y (fst w), HV x y (snd w)).
Qed.

Definition Indiscrete_Top : TopSpace := {|
  top_carrier    := A;
  IsOpen         := indiscrete_open;
  open_respects  := indiscrete_respects;
  open_proper    := indiscrete_proper;
  open_union     := indiscrete_union;
  open_whole     := indiscrete_whole;
  open_inter     := indiscrete_inter
|}.

End Indiscrete.

(* Every setoid map into an indiscrete space is continuous.  The preimage of
   a uniform predicate is uniform, and by [open_uniform] every uniform
   predicate is open in every space. *)
Lemma into_indiscrete_continuous (X : TopSpace) (A : SetoidObject)
      (f : SetoidMorphism (top_carrier X) A) :
  Continuous X (Indiscrete_Top A) f.
Proof.
  intros U HU.
  apply open_uniform.
  intros x y Ufx.
  exact (HU (f x) (f y) Ufx).
Qed.

(* Dually, every setoid map out of a discrete space is continuous: the
   preimage of any open respects `≈` because the map does. *)
Lemma out_of_discrete_continuous (A : SetoidObject) (Y : TopSpace)
      (f : SetoidMorphism A (top_carrier Y)) :
  Continuous (Discrete_Top A) Y f.
Proof.
  intros U HU x y Hxy Ufx.
  exact (open_proper Y U HU (f x) (f y) (proper_morphism f x y Hxy) Ufx).
Qed.

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma const_proper (A B : SetoidObject) (b : B) :
  Proper (respectful equiv equiv) (fun _ : A => b).
Proof. intros u v Huv; reflexivity. Qed.

Definition const_morphism (A B : SetoidObject) (b : B) : SetoidMorphism A B := {|
  morphism        := fun _ => b;
  proper_morphism := const_proper A B b
|}.

(** ** Terminal and initial objects *)

(* The one-point space.  Its carrier is the singleton setoid used by
   [Sets_Terminal]; the topology is discrete (on a one-point carrier the
   discrete and indiscrete topologies agree). *)
Definition Point_Top : TopSpace := Discrete_Top unit_setoid_object.

(* Terminality.  The unique map sends everything to the point; its
   continuity is [open_const], since the preimage of any predicate on a
   single point is a CONSTANT predicate upstairs. *)
Definition top_one (X : TopSpace) : ContinuousMorphism X Point_Top := {|
  continuous_map := const_morphism (top_carrier X) (top_carrier Point_Top) ttt;
  continuity := fun U _ => open_const X (U ttt)
|}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma top_one_unique@{o h p}
  (X : TopSpace@{o}) (f g : X ~{Top@{h o}}~> Point_Top@{o}) : f ≈ g.
Proof.
  intro x.
  destruct (continuous_map f x), (continuous_map g x); reflexivity.
Qed.

#[export]
Program Instance Top_Terminal@{o h p} : @Terminal Top@{h o} := {
  terminal_obj := Point_Top@{o};
  one := @top_one@{h o};
  one_unique := @top_one_unique@{o h p}
}.

(* The empty space: carrier [False], every predicate open (vacuously, since
   the discrete condition quantifies over points that do not exist). *)
Definition Empty_Top : TopSpace :=
  Discrete_Top {| carrier := False; is_setoid := False_Setoid |}.

Definition empty_map (X : TopSpace) :
  SetoidMorphism (top_carrier Empty_Top) (top_carrier X).
Proof.
  refine {| morphism := fun z : False => False_rect _ z |}.
  repeat intro; contradiction.
Defined.

Definition top_zero (X : TopSpace) : ContinuousMorphism Empty_Top X.
Proof.
  refine {| continuous_map := empty_map X |}.
  intros U HU; repeat intro; contradiction.
Defined.

(* Any two maps out of the empty space agree, there being no point at which
   they could differ. *)
Lemma top_zero_unique (X : TopSpace) (f g : Empty_Top ~{Top}~> X) : f ≈ g.
Proof. intro z; contradiction. Qed.

#[export]
Program Instance Top_Initial : @Initial Top := {
  terminal_obj := Empty_Top;
  one := top_zero;
  one_unique := top_zero_unique
}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Top_no_zero_object : @ZeroObject Top → False.
Proof.
  intros [T I coincide].
  exact (continuous_map (@zero _ I Empty_Top)
           (from coincide (continuous_map (@one _ T Point_Top) ttt))).
Qed.

(* The concrete instance of the same fact: the chosen terminal and initial
   objects themselves are not isomorphic. *)
Example point_not_iso_empty : Point_Top ≅[Top] Empty_Top → False.
Proof. intro iso; exact (continuous_map (to iso) ttt). Qed.

(** ** Monomorphisms are the injections *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition top_point (X : TopSpace) (a : X) :
  ContinuousMorphism Point_Top X := {|
  continuous_map := const_morphism (top_carrier Point_Top) (top_carrier X) a;
  continuity := fun U _ => open_const Point_Top (U a)
|}.

Theorem top_monic_iff {X Y : TopSpace} (f : X ~{Top}~> Y) :
  (∀ a b : X, f a ≈ f b → a ≈ b) ↔ Monic f.
Proof.
  split.
  - intros Hinj.
    constructor; intros Z g1 g2 Hg z.
    exact (Hinj (continuous_map g1 z) (continuous_map g2 z) (Hg z)).
  - intros [Hmonic] a b Hab.
    exact (Hmonic Point_Top (top_point X a) (top_point X b)
                  (fun _ => Hab) ttt).
Qed.

(** ** Epimorphisms are the surjections *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition InImage {X Y : TopSpace} (f : X ~{Top}~> Y) (b : Y) : Type :=
  ∃ a : X, f a ≈ b.

(* The image predicate respects the codomain's equality. *)
Lemma InImage_respects {X Y : TopSpace} (f : X ~{Top}~> Y) (b b' : Y) :
  b ≈ b' → InImage f b → InImage f b'.
Proof.
  intros Hbb w.
  exact (projT1 w; transitivity (projT2 w) Hbb).
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CokernelPair.

Context {X Y : TopSpace}.
Context (f : X ~{Top}~> Y).

(* The glued carrier: two copies of the points of Y. *)
Definition CP_point : Type := Datatypes.sum (carrier (top_carrier Y))
                                            (carrier (top_carrier Y)).

(* The gluing relation.  Within a copy it is Y's own equality; across the
   copies it additionally demands membership in the image of f. *)
Definition CP_rel (u v : CP_point) : Type :=
  match u, v with
  | Datatypes.inl y, Datatypes.inl y' => y ≈ y'
  | Datatypes.inr y, Datatypes.inr y' => y ≈ y'
  | Datatypes.inl y, Datatypes.inr y' => (y ≈ y') ∧ InImage f y
  | Datatypes.inr y, Datatypes.inl y' => (y ≈ y') ∧ InImage f y
  end.

Lemma CP_rel_refl : Reflexive CP_rel.
Proof. intros [y|y]; simpl; reflexivity. Qed.

Lemma CP_rel_sym : Symmetric CP_rel.
Proof.
  intros [y|y] [y'|y'] H; simpl in *.
  - now symmetry.
  - exact (symmetry (fst H), InImage_respects f y y' (fst H) (snd H)).
  - exact (symmetry (fst H), InImage_respects f y y' (fst H) (snd H)).
  - now symmetry.
Qed.

Lemma CP_rel_trans : Transitive CP_rel.
Proof.
  intros [a|a] [b|b] [c|c] H1 H2; simpl in *.
  (* inl inl inl *) - now transitivity b.
  (* inl inl inr *) - exact (transitivity H1 (fst H2),
                             InImage_respects f b a (symmetry H1) (snd H2)).
  (* inl inr inl *) - exact (transitivity (fst H1) (fst H2)).
  (* inl inr inr *) - exact (transitivity (fst H1) H2, snd H1).
  (* inr inl inl *) - exact (transitivity (fst H1) H2, snd H1).
  (* inr inl inr *) - exact (transitivity (fst H1) (fst H2)).
  (* inr inr inl *) - exact (transitivity H1 (fst H2),
                             InImage_respects f b a (symmetry H1) (snd H2)).
  (* inr inr inr *) - now transitivity b.
Qed.

Definition CP_Setoid : Setoid CP_point := {|
  equiv := CP_rel;
  setoid_equiv := Build_Equivalence CP_rel CP_rel_refl CP_rel_sym CP_rel_trans
|}.

Definition CP_carrier : SetoidObject :=
  {| carrier := CP_point; is_setoid := CP_Setoid |}.

(* A glued predicate is open when it respects the gluing and restricts to
   an open along each of the two legs. *)
Definition CP_open (W : CP_carrier → Type) : Type :=
  ((∀ u v, CP_rel u v → W u → W v)
     ∧ IsOpen Y (fun y => W (Datatypes.inl y))
     ∧ IsOpen Y (fun y => W (Datatypes.inr y)))%type.

Lemma CP_respects (W W' : CP_carrier → Type) :
  (∀ u, W u ↔ W' u) → CP_open W → CP_open W'.
Proof.
  intros HW HO.
  refine (_, (_, _)).
  - intros u v Huv W'u.
    exact (fst (HW v) (fst HO u v Huv (snd (HW u) W'u))).
  - exact (open_respects Y _ _ (fun y => HW (Datatypes.inl y)) (fst (snd HO))).
  - exact (open_respects Y _ _ (fun y => HW (Datatypes.inr y)) (snd (snd HO))).
Qed.

Lemma CP_proper (W : CP_carrier → Type) :
  CP_open W → ∀ u v : CP_carrier, u ≈ v → W u → W v.
Proof. intros HO u v Huv; exact (fst HO u v Huv). Qed.

Lemma CP_union (I : Type) (W : I → (CP_carrier → Type)) :
  (∀ i, CP_open (W i)) → CP_open (fun u => { i : I & W i u }).
Proof.
  intro HW.
  refine (_, (_, _)).
  - intros u v Huv w.
    exact (projT1 w; fst (HW (projT1 w)) u v Huv (projT2 w)).
  - exact (open_union Y I (fun i y => W i (Datatypes.inl y))
                      (fun i => fst (snd (HW i)))).
  - exact (open_union Y I (fun i y => W i (Datatypes.inr y))
                      (fun i => snd (snd (HW i)))).
Qed.

Lemma CP_whole : CP_open (fun _ => poly_unit).
Proof. exact (fun _ _ _ w => w, (open_whole Y, open_whole Y)). Qed.

Lemma CP_inter (W W' : CP_carrier → Type) :
  CP_open W → CP_open W' → CP_open (fun u => W u ∧ W' u).
Proof.
  intros HO HO'.
  refine (_, (_, _)).
  - intros u v Huv w.
    exact (fst HO u v Huv (fst w), fst HO' u v Huv (snd w)).
  - exact (open_inter Y _ _ (fst (snd HO)) (fst (snd HO'))).
  - exact (open_inter Y _ _ (snd (snd HO)) (snd (snd HO'))).
Qed.

Definition CokernelPair : TopSpace := {|
  top_carrier   := CP_carrier;
  IsOpen        := CP_open;
  open_respects := CP_respects;
  open_proper   := CP_proper;
  open_union    := CP_union;
  open_whole    := CP_whole;
  open_inter    := CP_inter
|}.

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CP_inl : SetoidMorphism (top_carrier Y) CP_carrier.
Proof.
  refine {| morphism := Datatypes.inl |}.
  intros u v Huv; exact Huv.
Defined.

Definition CP_inr : SetoidMorphism (top_carrier Y) CP_carrier.
Proof.
  refine {| morphism := Datatypes.inr |}.
  intros u v Huv; exact Huv.
Defined.

Definition CP_leftLeg : ContinuousMorphism Y CokernelPair :=
  Build_ContinuousMorphism Y CokernelPair CP_inl (fun W HW => fst (snd HW)).

Definition CP_rightLeg : ContinuousMorphism Y CokernelPair :=
  Build_ContinuousMorphism Y CokernelPair CP_inr (fun W HW => snd (snd HW)).

(* The defining coequalizing property: the legs agree after f, because at a
   point of the image the gluing relation holds — witnessed by the very
   preimage that puts the point in the image. *)
Lemma CP_legs_agree :
  CP_leftLeg ∘[Top] f ≈ CP_rightLeg ∘[Top] f.
Proof.
  intro a; simpl.
  refine (_, _).
  - reflexivity.
  - refine (a; _); reflexivity.
Qed.

End CokernelPair.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem top_epic_iff {X Y : TopSpace} (f : X ~{Top}~> Y) :
  (∀ b : Y, ∃ a : X, f a ≈ b) ↔ Epic f.
Proof.
  split.
  - intros Hsurj.
    constructor; intros Z g1 g2 Hg b.
    destruct (Hsurj b) as [a Ha].
    rewrite <- Ha.
    exact (Hg a).
  - intros [Hepic] b.
    exact (snd (Hepic (CokernelPair f) (CP_leftLeg f) (CP_rightLeg f)
                      (CP_legs_agree f) b)).
Qed.

(* The same statement in cokernel-pair form, naming the construction that
   does the work. *)
Theorem top_epic_surjective_via_cokernel_pair
        {X Y : TopSpace} (f : X ~{Top}~> Y) :
  Epic f → ∀ b : Y, InImage f b.
Proof. intro He; exact (snd (top_epic_iff f) He). Qed.

(** ** The classical two-point probe, and its constructive status *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition bool_setoid_object : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

(* The two-point indiscrete space used as the probe.  Every setoid map into
   it is continuous ([into_indiscrete_continuous]), which is the only
   property of it the argument uses. *)
Definition TwoPoint_Indiscrete : TopSpace := Indiscrete_Top bool_setoid_object.

Section IndiscreteProbe.

Context {X Y : TopSpace}.
Context (f : X ~{Top}~> Y).
Context (dec : ∀ b : Y, InImage f b ∨ ¬ (InImage f b)).

(* The characteristic function of the image, read off the decision. *)
Definition image_char (b : Y) : bool :=
  match dec b with
  | Datatypes.inl _ => true
  | Datatypes.inr _ => false
  end.

Definition image_char_setoid_map :
  SetoidMorphism (top_carrier Y) bool_setoid_object.
Proof using X Y dec f.
  refine {| morphism := image_char |}.
  intros b b' Hbb; unfold image_char.
  destruct (dec b) as [w|n], (dec b') as [w'|n'].
  - reflexivity.
  - destruct (n' (InImage_respects f b b' Hbb w)).
  - destruct (n (InImage_respects f b' b (symmetry Hbb) w')).
  - reflexivity.
Defined.

Definition image_char_map : ContinuousMorphism Y TwoPoint_Indiscrete :=
  Build_ContinuousMorphism Y TwoPoint_Indiscrete image_char_setoid_map
    (into_indiscrete_continuous Y bool_setoid_object image_char_setoid_map).

Definition always_true_setoid_map :
  SetoidMorphism (top_carrier Y) bool_setoid_object :=
  const_morphism (top_carrier Y) bool_setoid_object true.

Definition always_true_map : ContinuousMorphism Y TwoPoint_Indiscrete :=
  Build_ContinuousMorphism Y TwoPoint_Indiscrete always_true_setoid_map
    (into_indiscrete_continuous Y bool_setoid_object always_true_setoid_map).

(* The classical route, made honest: under [dec], an epi is surjective. *)
Theorem top_epic_surjective_via_indiscrete :
  Epic f → ∀ b : Y, InImage f b.
Proof using X Y dec f.
  intros [Hepic] b.
  assert (Hagree : always_true_map ∘[Top] f ≈ image_char_map ∘[Top] f).
  { intro a; simpl; unfold image_char.
    destruct (dec (continuous_map f a)) as [w|n].
    - reflexivity.
    - exfalso; apply n; refine (a; _); reflexivity. }
  pose proof (Hepic TwoPoint_Indiscrete always_true_map image_char_map Hagree b)
    as Heq.
  simpl in Heq; unfold image_char in Heq.
  destruct (dec b) as [w|n].
  - exact w.
  - discriminate Heq.
Qed.

End IndiscreteProbe.

(** ** Open covers *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Covers {X : TopSpace} {I : Type}
           (U : I → (X → Type)) (V : X → Type) : Type :=
  ((∀ i, IsOpen X (U i)) ∧ (∀ x : X, V x ↔ ∃ i : I, U i x))%type.

(* The empty family covers the empty predicate — the nullary instance of the
   definition: with no members the union is empty, so what the family covers
   is exactly the empty predicate. *)
Definition covers_nothing (X : TopSpace) :
  Covers (X:=X) (I:=False) (fun _ _ => False) (fun _ => False).
Proof.
  split.
  - intro i; contradiction.
  - intro x; split.
    + contradiction.
    + intro w; exact (projT2 w).
Defined.

(* The one-member family consisting of the whole space covers the whole
   space. *)
Definition covers_whole (X : TopSpace) :
  Covers (X:=X) (I:=poly_unit) (fun _ _ => poly_unit) (fun _ => poly_unit).
Proof.
  split.
  - intro i; exact (open_whole X).
  - intro x; split.
    + intro w; exact (ttt; w).
    + intro w; exact (projT2 w).
Defined.

(** ** Separation and compactness *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsHausdorff (X : TopSpace) : Type :=
  ∀ x y : X, ¬ (x ≈ y) →
    ∃ U : X → Type, ∃ V : X → Type,
      ((IsOpen X U ∧ IsOpen X V)
         ∧ (U x ∧ V y)
         ∧ (∀ z : X, U z → V z → False))%type.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsCompact (X : TopSpace) : Type :=
  ∀ (I : Type) (U : I → (X → Type)),
    Covers U (fun _ => poly_unit) →
    ∃ l : list I, ∀ x : X, ∃ i : I, (List.In i l ∧ U i x)%type.

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Point_Compact : IsCompact Point_Top.
Proof.
  intros I U HU.
  destruct (fst (snd HU ttt) ttt) as [i Hi].
  refine (Datatypes.cons i Datatypes.nil; _).
  intro x; destruct x.
  refine (i; _); split.
  - left; reflexivity.
  - exact Hi.
Qed.

Lemma Point_Hausdorff : IsHausdorff Point_Top.
Proof.
  intros x y Hxy; destruct x, y.
  exfalso; apply Hxy; reflexivity.
Qed.

(*
   本节说明层/筛、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Hausdorff_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => IsHausdorff X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition HausdorffSpaces : Category := Sub Top Hausdorff_Subcategory.

Lemma Hausdorff_Full :
  Category.Construction.Subcategory.Full Top Hausdorff_Subcategory.
Proof. intros x y ox oy g; exact I. Qed.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CompactHausdorff_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => (IsCompact X ∧ IsHausdorff X)%type)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CompactHausdorffSpaces : Category :=
  Sub Top CompactHausdorff_Subcategory.

Lemma CompactHausdorff_Full :
  Category.Construction.Subcategory.Full Top CompactHausdorff_Subcategory.
Proof. intros x y ox oy g; exact I. Qed.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity: a two-point discrete space, and what it distinguishes *)

(*
   本节说明 Top 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Bool_Discrete : TopSpace := Discrete_Top bool_setoid_object.

Lemma singleton_true_open :
  IsOpen Bool_Discrete (fun b : bool_setoid_object => b = true).
Proof. intros x y Hxy Hx; simpl in Hxy; now subst. Qed.

Theorem indiscrete_to_discrete_id_not_continuous :
  Continuous TwoPoint_Indiscrete Bool_Discrete setoid_morphism_id → False.
Proof.
  intro Hc.
  pose proof (Hc (fun b : bool_setoid_object => b = true)
                 singleton_true_open) as H.
  simpl in H.
  specialize (H true false eq_refl).
  discriminate.
Qed.

Theorem Bool_Discrete_Hausdorff : IsHausdorff Bool_Discrete.
Proof.
  intros x y Hxy.
  exists (fun z : bool_setoid_object => z = x).
  exists (fun z : bool_setoid_object => z = y).
  repeat split.
  - intros u v Huv Hu; simpl in Huv; now subst.
  - intros u v Huv Hu; simpl in Huv; now subst.
  - intros z Hz Hz'; simpl in *; subst; apply Hxy; reflexivity.
Qed.

Theorem TwoPoint_Indiscrete_not_Hausdorff :
  IsHausdorff TwoPoint_Indiscrete → False.
Proof.
  intro H.
  destruct (H true false ltac:(simpl; discriminate))
    as [U [V [[HU HV] [[Ut Vf] Hdisj]]]].
  exact (Hdisj false (HU true false Ut) Vf).
Qed.

(* Negation is a continuous nonidentity endomap of the discrete two-point
   space; the constant-true endomap is continuous by [open_const]. *)
Definition negb_setoid : SetoidMorphism bool_setoid_object bool_setoid_object.
Proof. refine {| morphism := negb |}. Defined.

Definition negb_map : Bool_Discrete ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism Bool_Discrete Bool_Discrete negb_setoid
    (out_of_discrete_continuous bool_setoid_object Bool_Discrete negb_setoid).

Definition const_true_map : Bool_Discrete ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism Bool_Discrete Bool_Discrete
    (const_morphism bool_setoid_object bool_setoid_object true)
    (fun U _ => open_const Bool_Discrete (U true)).

Lemma negb_map_not_id : negb_map ≈ @id Top Bool_Discrete → False.
Proof. intro H; pose proof (H true) as Ht; simpl in Ht; discriminate. Qed.

Theorem const_true_not_monic : Monic const_true_map → False.
Proof.
  intro Hm.
  pose proof (snd (top_monic_iff const_true_map) Hm) as Hinj.
  pose proof (Hinj true false eq_refl) as H; simpl in H; discriminate.
Qed.

Theorem const_true_not_epic : Epic const_true_map → False.
Proof.
  intro He.
  pose proof (snd (top_epic_iff const_true_map) He false) as w.
  destruct w as [a Ha]; simpl in Ha; discriminate.
Qed.

Theorem id_monic_and_epic :
  (Monic (@id Top Bool_Discrete) * Epic (@id Top Bool_Discrete))%type.
Proof.
  split.
  - apply top_monic_iff; intros a b H; exact H.
  - apply top_epic_iff; intro b; exists b; reflexivity.
Qed.
