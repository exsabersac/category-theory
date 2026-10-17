Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

Open Scope category_scope.

(** * Finite index categories and finite limits *)

(*
   本文件给出有限情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Finite index categories *)

Section FiniteCategory.

Context {J : Category}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record ArrowHit (a : @ArrowIx J) {x y : J} (f : x ~{J}~> y) : Type := {
  hit_dom : aix_dom a = x;
  hit_cod : aix_cod a = y;
  hit_arr : hom_cast hit_dom hit_cod (aix_arr a) ≈ f
}.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record FiniteCategory : Type := {
  fc_size  : nat;
  fc_arr   : Fin.t fc_size → @ArrowIx J;
  fc_cover : ∀ (x y : J) (f : x ~{J}~> y),
    { i : Fin.t fc_size & ArrowHit (fc_arr i) f }
}.

(* The family the enumeration presents, in the form [Generates] takes. *)

Definition fc_dom (F : FiniteCategory) (i : Fin.t (fc_size F)) : J :=
  aix_dom (fc_arr F i).

Definition fc_cod (F : FiniteCategory) (i : Fin.t (fc_size F)) : J :=
  aix_cod (fc_arr F i).

Definition fc_arrow (F : FiniteCategory) (i : Fin.t (fc_size F)) :
  fc_dom F i ~{J}~> fc_cod F i :=
  aix_arr (fc_arr F i).

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem fc_Generates (F : FiniteCategory) : Generates (fc_arrow F).
Proof.
  intros x y f.
  destruct (fc_cover F x y f) as [i [ed ec ea]].
  destruct ed, ec.
  exact (gen_equiv _ f ea (gen_idx i)).
Qed.

(** *** Finitely many objects *)

(* Objects inject into identity arrows, so an enumeration of the arrows
   yields one of the objects: the object [x] is recovered as the DOMAIN of
   the arrow that hits [id[x]]. *)

Definition fc_obj_idx (F : FiniteCategory) (x : J) : Fin.t (fc_size F) :=
  `1 (fc_cover F x x id).

Definition fc_obj_rt (F : FiniteCategory) (x : J) :
  fc_dom F (fc_obj_idx F x) = x :=
  hit_dom _ _ (`2 (fc_cover F x x id)).

(* Finitely many objects, as a retraction of a [Fin.t] onto them. *)

Record FiniteObjects : Type := {
  fo_size : nat;
  fo_obj  : Fin.t fo_size → J;
  fo_idx  : J → Fin.t fo_size;
  fo_rt   : ∀ x : J, fo_obj (fo_idx x) = x
}.

(* Fong–Spivak §6.2.4's footnote: a category with finitely many morphisms
   has finitely many objects. *)

Definition finite_morphisms_implies_finite_objects (F : FiniteCategory) :
  FiniteObjects := {|
  fo_size := fc_size F;
  fo_obj  := fc_dom F;
  fo_idx  := fc_obj_idx F;
  fo_rt   := fc_obj_rt F
|}.

End FiniteCategory.

Arguments ArrowHit {J} a {x y} f.
Arguments hit_dom {J a x y f} _.
Arguments hit_cod {J a x y f} _.
Arguments hit_arr {J a x y f} _.
Arguments FiniteCategory J : clear implicits.
Arguments FiniteObjects J : clear implicits.
Arguments fc_size {J} _.
Arguments fc_arr {J} _ _.
Arguments fc_cover {J} _ {x y} f.
Arguments fc_dom {J} _ _.
Arguments fc_cod {J} _ _.
Arguments fc_arrow {J} _ _.
Arguments fc_obj_idx {J} _ _.
Arguments fc_obj_rt {J} _ _.
Arguments fo_size {J} _.
Arguments fo_obj {J} _ _.
Arguments fo_idx {J} _ _.
Arguments fo_rt {J} _ _.

(** *** Finiteness is self-dual *)

(* An arrow of [J^op] is an arrow of [J] with its endpoints exchanged, so the
   same list enumerates both. *)

Definition FiniteCategory_op {J : Category} (F : FiniteCategory J) :
  FiniteCategory (J^op).
Proof.
  unshelve refine {|
    fc_size := fc_size F;
    fc_arr := fun i =>
      @mk_arrow (J^op) (aix_cod (fc_arr F i)) (aix_dom (fc_arr F i))
        (aix_arr (fc_arr F i))
  |}.
  intros x y f.
  destruct (fc_cover F (x := y) (y := x) f) as [i [ed ec ea]].
  exists i.
  unshelve econstructor.
  - exact ec.
  - exact ed.
  - cbn; destruct ec, ed; exact ea.
Defined.

(** ** Products over a retract of an index *)

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RetractProduct.

#[local] Set Default Proof Using "All".

Context {C : Category}.
Context {A B : Type} (down : A → B) (idx : B → A)
  (rt : ∀ b : B, down (idx b) = b).
Context (fam : B → C).
Context {P : C} (proj : ∀ a : A, P ~> fam (down a))
  (HP : IsIndexedProduct (fun a : A => fam (down a)) P proj).

(* The transport along the retraction, as a cast. *)

Definition rp_cast (b : B) : fam (down (idx b)) ~> fam b :=
  id_cast (f_equal fam (rt b)).

Lemma rp_cast_family {c : C} (h : ∀ b : B, c ~> fam b) (b : B) :
  rp_cast b ∘ h (down (idx b)) ≈ h b.
Proof.
  unfold rp_cast.
  generalize (rt b).
  generalize (down (idx b)).
  intros b' e.
  destruct e.
  cat.
Qed.

(* The comparison [r : P ~> P] that reads every factor off its canonical
   representative. *)

Definition rp_r : P ~> P :=
  unique_obj (iprod_desc HP (fun a => rp_cast (down a) ∘ proj (idx (down a)))).

Lemma rp_r_proj (a : A) :
  proj a ∘ rp_r ≈ rp_cast (down a) ∘ proj (idx (down a)).
Proof. exact (unique_property (iprod_desc HP _) a). Qed.

(* An equalizer of [id] and [r]. *)

Context {E : C} (e : E ~> P) (HE : IsEqualizer id rp_r E e).

Definition rp_proj (b : B) : E ~> fam b :=
  rp_cast b ∘ proj (idx b) ∘ e.

Lemma rp_r_e : rp_r ∘ e ≈ e.
Proof.
  pose proof (fork_eq HE) as H.
  rewrite id_left in H.
  now symmetry.
Qed.

Definition rp_tuple {c : C} (h : ∀ b : B, c ~> fam b) : c ~> P :=
  unique_obj (iprod_desc HP (fun a => h (down a))).

Lemma rp_tuple_proj {c : C} (h : ∀ b : B, c ~> fam b) (a : A) :
  proj a ∘ rp_tuple h ≈ h (down a).
Proof. exact (unique_property (iprod_desc HP _) a). Qed.

Lemma rp_tuple_equalizes {c : C} (h : ∀ b : B, c ~> fam b) :
  id ∘ rp_tuple h ≈ rp_r ∘ rp_tuple h.
Proof.
  apply (pe_iprod_ext HP); intro a.
  rewrite id_left, rp_tuple_proj.
  rewrite comp_assoc, rp_r_proj, <- comp_assoc, rp_tuple_proj.
  symmetry; apply (rp_cast_family h).
Qed.

Definition rp_med {c : C} (h : ∀ b : B, c ~> fam b) : c ~> E :=
  unique_obj (eq_desc HE (rp_tuple h) (rp_tuple_equalizes h)).

Lemma rp_med_incl {c : C} (h : ∀ b : B, c ~> fam b) :
  e ∘ rp_med h ≈ rp_tuple h.
Proof. exact (unique_property (eq_desc HE _ _)). Qed.

Lemma rp_med_proj {c : C} (h : ∀ b : B, c ~> fam b) (b : B) :
  rp_proj b ∘ rp_med h ≈ h b.
Proof.
  unfold rp_proj.
  rewrite <- comp_assoc, rp_med_incl.
  rewrite <- comp_assoc, rp_tuple_proj.
  apply (rp_cast_family h).
Qed.

Lemma rp_med_unique {c : C} (h : ∀ b : B, c ~> fam b) (v : c ~> E)
  (Hv : ∀ b : B, rp_proj b ∘ v ≈ h b) :
  rp_med h ≈ v.
Proof.
  apply (monic (Monic := equalizer_monic id rp_r HE)).
  rewrite rp_med_incl.
  apply (pe_iprod_ext HP); intro a.
  rewrite rp_tuple_proj.
  rewrite <- (Hv (down a)).
  unfold rp_proj.
  transitivity (proj a ∘ ((rp_r ∘ e) ∘ v)).
  - rewrite comp_assoc, comp_assoc, rp_r_proj.
    reflexivity.
  - rewrite rp_r_e.
    reflexivity.
Qed.

Definition rp_IsIndexedProduct : IsIndexedProduct fam E rp_proj := {|
  iprod_desc := fun c h => {|
    unique_obj      := rp_med h;
    unique_property := rp_med_proj h;
    uniqueness      := rp_med_unique h |}
|}.

End RetractProduct.

(* With a supply of equalizers, the product over the retract is CHOSEN. *)

Section RetractProductChosen.

Context {C : Category} (HEq : HasEqualizers C).
Context {A B : Type} (down : A → B) (idx : B → A)
  (rt : ∀ b : B, down (idx b) = b).
Context (fam : B → C).
Context {P : C} (proj : ∀ a : A, P ~> fam (down a))
  (HP : IsIndexedProduct (fun a : A => fam (down a)) P proj).

Definition retract_equalizer :=
  @equalizer C HEq P P id (rp_r down idx rt fam proj HP).

Definition retract_product : C := `1 retract_equalizer.

Definition retract_incl : retract_product ~> P := `1 (`2 retract_equalizer).

Definition retract_product_proj (b : B) : retract_product ~> fam b :=
  rp_proj down idx rt fam proj retract_incl b.

Definition retract_product_ump :
  IsIndexedProduct fam retract_product retract_product_proj :=
  rp_IsIndexedProduct down idx rt fam proj HP retract_incl
    (`2 (`2 retract_equalizer)).

End RetractProductChosen.

(** ** The corollary: finite products and equalizers give every finite limit *)

Section FiniteLimit.

#[local] Set Default Proof Using "All".

Context {C : Category} (HFP : HasFiniteProducts C) (HEq : HasEqualizers C).
Context {J : Category} (HJ : FiniteCategory J) (F : J ⟶ C).

(* The product over the enumeration's DOMAINS, then over the objects of [J]
   as their retract. *)

Definition fl_ofam (i : Fin.t (fc_size HJ)) : C := F (fc_dom HJ i).

Definition fl_P0 : C := finite_product fl_ofam.
Definition fl_P0_proj (i : Fin.t (fc_size HJ)) : fl_P0 ~> fl_ofam i :=
  finite_product_proj fl_ofam i.
Definition fl_P0_ump : IsIndexedProduct fl_ofam fl_P0 fl_P0_proj :=
  finite_product_ump fl_ofam.

Definition fl_P : C :=
  retract_product HEq (fc_dom HJ) (fc_obj_idx HJ) (fc_obj_rt HJ)
    (fun x : J => F x) fl_P0_proj fl_P0_ump.

Definition fl_P_proj (x : J) : fl_P ~> F x :=
  retract_product_proj HEq (fc_dom HJ) (fc_obj_idx HJ) (fc_obj_rt HJ)
    (fun x : J => F x) fl_P0_proj fl_P0_ump x.

Definition fl_P_ump : IsIndexedProduct (fun x : J => F x) fl_P fl_P_proj :=
  retract_product_ump HEq (fc_dom HJ) (fc_obj_idx HJ) (fc_obj_rt HJ)
    (fun x : J => F x) fl_P0_proj fl_P0_ump.

(* The product over the enumerated ARROWS, at their codomains. *)

Definition fl_afam (i : Fin.t (fc_size HJ)) : C := F (fc_cod HJ i).

Definition fl_Q : C := finite_product fl_afam.
Definition fl_Q_proj (i : Fin.t (fc_size HJ)) : fl_Q ~> fl_afam i :=
  finite_product_proj fl_afam i.
Definition fl_Q_ump : IsIndexedProduct fl_afam fl_Q fl_Q_proj :=
  finite_product_ump fl_afam.

(* The two canonical maps, by their components. *)

Definition fl_s : fl_P ~> fl_Q :=
  unique_obj (iprod_desc fl_Q_ump (fun i => fl_P_proj (fc_cod HJ i))).

Definition fl_t : fl_P ~> fl_Q :=
  unique_obj (iprod_desc fl_Q_ump
    (fun i => fmap[F] (fc_arrow HJ i) ∘ fl_P_proj (fc_dom HJ i))).

Lemma fl_s_proj (i : Fin.t (fc_size HJ)) :
  fl_Q_proj i ∘ fl_s ≈ fl_P_proj (fc_cod HJ i).
Proof. exact (unique_property (iprod_desc fl_Q_ump _) i). Qed.

Lemma fl_t_proj (i : Fin.t (fc_size HJ)) :
  fl_Q_proj i ∘ fl_t ≈ fmap[F] (fc_arrow HJ i) ∘ fl_P_proj (fc_dom HJ i).
Proof. exact (unique_property (iprod_desc fl_Q_ump _) i). Qed.

(* Their equalizer, and the limit. *)

Definition fl_eq := @equalizer C HEq _ _ fl_s fl_t.
Definition fl_apex : C := `1 fl_eq.
Definition fl_incl : fl_apex ~> fl_P := `1 (`2 fl_eq).
Definition fl_incl_IsEqualizer : IsEqualizer fl_s fl_t fl_apex fl_incl :=
  `2 (`2 fl_eq).

Definition fl_cone : Cone F :=
  pe_cone F fl_P_proj fl_P_ump (fc_Generates HJ) fl_Q_proj fl_Q_ump
    fl_s fl_t fl_s_proj fl_t_proj fl_incl fl_incl_IsEqualizer.

Definition fl_limiting : IsLimitCone fl_cone :=
  pe_limiting F fl_P_proj fl_P_ump (fc_Generates HJ) fl_Q_proj fl_Q_ump
    fl_s fl_t fl_s_proj fl_t_proj fl_incl fl_incl_IsEqualizer.

Definition finite_limit : Limit F := limitcone_limit fl_cone fl_limiting.

Example finite_limit_apex :
  vertex_obj[@limit_cone _ _ _ finite_limit] = fl_apex := eq_refl.

Example finite_limit_leg (x : J) :
  @vertex_map _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ finite_limit)) x
    = fl_P_proj x ∘ fl_incl := eq_refl.

End FiniteLimit.

(** ** Finite completeness *)

Definition FinitelyComplete {C : Category} : Type :=
  ∀ (J : Category) (HJ : FiniteCategory J) (F : J ⟶ C), Limit F.

Definition FinitelyCocomplete {C : Category} : Type :=
  ∀ (J : Category) (HJ : FiniteCategory J) (F : J ⟶ C), Colimit F.

Definition Complete_FinitelyComplete {C : Category} (HC : @Complete C) :
  @FinitelyComplete C :=
  fun J _ F => HC J F.

Definition Cocomplete_FinitelyCocomplete {C : Category} (HC : @Cocomplete C) :
  @FinitelyCocomplete C :=
  fun J _ F => HC J F.

Definition finitely_complete_from_finite_products {C : Category}
  (HFP : HasFiniteProducts C) (HEq : HasEqualizers C) : @FinitelyComplete C :=
  fun J HJ F => finite_limit HFP HEq HJ F.

(* Mac Lane §V.2 Corollary 1, the pinned name: a terminal object, binary
   products and equalizers give every finite limit. *)

Definition finitely_complete_from_generators {C : Category}
  (T : @Terminal C) (CP : @Cartesian C) (HEq : HasEqualizers C) :
  @FinitelyComplete C :=
  finitely_complete_from_finite_products
    (Cartesian_Terminal_HasFiniteProducts CP T) HEq.

(* The dual, at [C^op]. *)

Definition finitely_cocomplete_from_generators {C : Category}
  (I : @Initial C) (CO : @Cocartesian C) (HCo : HasCoequalizers C) :
  @FinitelyCocomplete C :=
  fun J HJ F =>
    @finitely_complete_from_generators (C^op) I CO
      (HasEqualizers_op_of_HasCoequalizers HCo)
      (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

(* Riehl §3.5 Theorem 3.5.17: pullbacks and a terminal object give every
   finite limit; dually, pushouts and an initial object give every finite
   colimit. *)

Definition finitely_complete_of_pullbacks_terminal {C : Category}
  (HPB : HasPullbacks C) (T : @Terminal C) : @FinitelyComplete C :=
  finitely_complete_from_generators T
    (@Cartesian_of_HasPullbacks_Terminal C T HPB)
    (@HasEqualizers_of_HasPullbacks_Terminal C T HPB).

Definition finitely_cocomplete_of_pushouts_initial {C : Category}
  (HPO : HasPushouts C) (I : @Initial C) : @FinitelyCocomplete C :=
  fun J HJ F =>
    @finitely_complete_of_pullbacks_terminal (C^op)
      (HasPullbacks_op_of_HasPushouts HPO) I
      (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

(** ** The converse: a finitely complete category has the generators *)

(** *** The empty shape and the terminal object *)

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition EmptyShape@{o h} : Category@{o h h} := DiscreteCat@{o h h} False.

Definition EmptyShape_FiniteCategory@{o h u +} :
  FiniteCategory@{o h u} EmptyShape@{o h} := {|
  fc_size  := 0;
  fc_arr   := fin0_rect (fun _ => @ArrowIx EmptyShape@{o h});
  fc_cover := fun x => False_rect _ x
|}.

Definition EmptyDiagram@{o h co ch +} (C : Category@{co ch ch}) :
  EmptyShape@{o h} ⟶ C.
Proof.
  unshelve refine (@Build_Functor EmptyShape@{o h} C
    (fun x => False_rect _ x) (fun x y _ => False_rect _ x) _ _ _);
    intros; contradiction.
Defined.

Definition empty_cone@{o h co ch +} {C : Category@{co ch ch}} (c : C) :
  Cone (EmptyDiagram@{o h co ch} C).
Proof.
  unshelve refine (@Build_Cone EmptyShape@{o h} C (EmptyDiagram@{o h co ch} C) c
    (@Build_ACone EmptyShape@{o h} C c (EmptyDiagram@{o h co ch} C)
       (fun x => False_rect _ x) _));
    intros; contradiction.
Defined.

Definition FinitelyComplete_Terminal@{co ch +} {C : Category@{co ch ch}}
  (FC : @FinitelyComplete C) : @Terminal C.
Proof.
  pose (L := FC EmptyShape EmptyShape_FiniteCategory (EmptyDiagram C)).
  unshelve refine {|
    terminal_obj := vertex_obj[@limit_cone _ _ _ L];
    one := fun c => unique_obj (@ump_limits _ _ _ L (empty_cone c))
  |}.
  intros c f g.
  transitivity (unique_obj (@ump_limits _ _ _ L (empty_cone c))).
  - symmetry.
    exact (uniqueness (@ump_limits _ _ _ L (empty_cone c)) f
             (fun x => False_rect _ x)).
  - exact (uniqueness (@ump_limits _ _ _ L (empty_cone c)) g
             (fun x => False_rect _ x)).
Defined.

(** *** The walking cospan and pullbacks *)

Definition Roof_FiniteCategory : FiniteCategory Roof.
Proof.
  unshelve refine {|
    fc_size := 5;
    fc_arr := Vector.nth (Vector.of_list
      (@mk_arrow Roof RNeg RNeg IdNeg
       :: @mk_arrow Roof RZero RNeg ZeroNeg
       :: @mk_arrow Roof RZero RZero IdZero
       :: @mk_arrow Roof RZero RPos ZeroPos
       :: @mk_arrow Roof RPos RPos IdPos :: nil)%list)
  |}.
  intros x y f.
  destruct f.
  - exists Fin.F1.
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS Fin.F1).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS Fin.F1)).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
Defined.

Definition Cospan_FiniteCategory : FiniteCategory (Roof^op) :=
  FiniteCategory_op Roof_FiniteCategory.

Definition FinitelyComplete_HasPullbacks {C : Category}
  (FC : @FinitelyComplete C) : HasPullbacks C := {|
  pullback := fun (x y z : C) (f : x ~> z) (g : y ~> z) =>
    Pullback_to_Universal
      (Opposite_Functor (@ASpan (C^op) z x y f g))
      (FC (Roof^op) Cospan_FiniteCategory
         (Opposite_Functor (@ASpan (C^op) z x y f g)))
|}.

(* The other two generators follow through #326's reductions. *)

Definition FinitelyComplete_Cartesian {C : Category}
  (FC : @FinitelyComplete C) : @Cartesian C :=
  @Cartesian_of_HasPullbacks_Terminal C
    (FinitelyComplete_Terminal FC) (FinitelyComplete_HasPullbacks FC).

Definition FinitelyComplete_HasEqualizers {C : Category}
  (FC : @FinitelyComplete C) : HasEqualizers C :=
  @HasEqualizers_of_HasPullbacks_Terminal C
    (FinitelyComplete_Terminal FC) (FinitelyComplete_HasPullbacks FC).

Theorem FinitelyComplete_iff_pullbacks_terminal (C : Category) :
  @FinitelyComplete C ↔ (HasPullbacks C * @Terminal C)%type.
Proof.
  split.
  - intro FC.
    exact (FinitelyComplete_HasPullbacks FC, FinitelyComplete_Terminal FC).
  - intros [HPB T].
    exact (finitely_complete_of_pullbacks_terminal HPB T).
Defined.

(** *** The dual, by reading the primal at [C^op] *)

Definition FinitelyCocomplete_FinitelyComplete_op {C : Category}
  (FCC : @FinitelyCocomplete C) : @FinitelyComplete (C^op) :=
  fun J HJ F => FCC (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

Definition FinitelyComplete_op_FinitelyCocomplete {C : Category}
  (FC : @FinitelyComplete (C^op)) : @FinitelyCocomplete C :=
  fun J HJ F => FC (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

Definition FinitelyCocomplete_Initial {C : Category}
  (FCC : @FinitelyCocomplete C) : @Initial C :=
  FinitelyComplete_Terminal (FinitelyCocomplete_FinitelyComplete_op FCC).

Definition FinitelyCocomplete_HasPushouts {C : Category}
  (FCC : @FinitelyCocomplete C) : HasPushouts C :=
  HasPushouts_of_HasPullbacks_op
    (FinitelyComplete_HasPullbacks
       (FinitelyCocomplete_FinitelyComplete_op FCC)).

Theorem FinitelyCocomplete_iff_pushouts_initial (C : Category) :
  @FinitelyCocomplete C ↔ (HasPushouts C * @Initial C)%type.
Proof.
  split.
  - intro FCC.
    exact (FinitelyCocomplete_HasPushouts FCC, FinitelyCocomplete_Initial FCC).
  - intros [HPO I].
    exact (finitely_cocomplete_of_pushouts_initial HPO I).
Defined.

(** ** Sanity witnesses: the small shapes are finite *)

Definition Two_FiniteCategory : FiniteCategory _2.
Proof.
  unshelve refine {|
    fc_size := 3;
    fc_arr := Vector.nth (Vector.of_list
      (@mk_arrow _2 TwoX TwoX TwoIdX
       :: @mk_arrow _2 TwoY TwoY TwoIdY
       :: @mk_arrow _2 TwoX TwoY TwoXY :: nil)%list)
  |}.
  intros x y f.
  destruct f.
  - exists Fin.F1.
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS Fin.F1).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS Fin.F1)).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
Defined.

Definition Parallel_FiniteCategory : FiniteCategory Parallel.
Proof.
  unshelve refine {|
    fc_size := 4;
    fc_arr := Vector.nth (Vector.of_list
      (@mk_arrow Parallel ParX ParX (true; ParIdX) ::
       @mk_arrow Parallel ParY ParY (true; ParIdY) ::
       @mk_arrow Parallel ParX ParY (true; ParOne) ::
       @mk_arrow Parallel ParX ParY (false; ParTwo) :: nil)%list)
  |}.
  intros x y [b f].
  destruct f.
  - exists Fin.F1.
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS Fin.F1).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS Fin.F1)).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
Defined.
