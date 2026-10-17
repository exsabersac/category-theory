Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.Limit.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(** * The limit as a functor on the category of all diagrams *)

(*
   nLab: https://ncatlab.org/nlab/show/limit

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The category of all diagrams in a fixed target *)

(* An object: an index category together with a diagram of that shape. *)
Record DObj (C : Category) : Type := {
  didx  : Category;
  ddiag : didx ⟶ C
}.

Arguments didx {C} _.
Arguments ddiag {C} _.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record DHom {C : Category} (X Y : DObj C) : Type := {
  dW   : didx X ⟶ didx Y;
  dtau : ddiag Y ◯ dW ⟹ ddiag X
}.

Arguments dW {C X Y} _.
Arguments dtau {C X Y} _.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition DHom_equiv {C : Category} {X Y : DObj C} (f g : DHom X Y) : Type :=
  { i : ∀ j : didx X, dW f j ≅ dW g j
  & ((∀ (x y : didx X) (h : x ~> y),
        fmap[dW f] h ≈ from (i y) ∘ fmap[dW g] h ∘ to (i x))
     * (∀ j : didx X,
        transform[dtau f] j ≈ transform[dtau g] j ∘ fmap[ddiag Y] (to (i j))))%type }.

#[export] Program Instance DHom_Setoid {C : Category} {X Y : DObj C} :
  Setoid (DHom X Y) := {| equiv := DHom_equiv |}.
Next Obligation.
  constructor.
  - intro f.
    exists (fun j => iso_id).
    split; intros; simpl.
    + now rewrite id_left, id_right.
    + now rewrite fmap_id, id_right.
  - intros f g [i [Hm Ht]].
    exists (fun j => iso_sym (i j)).
    split; intros; simpl.
    + rewrite Hm.
      rewrite <- !comp_assoc.
      rewrite iso_to_from, id_right.
      rewrite comp_assoc, iso_to_from, id_left.
      reflexivity.
    + rewrite Ht.
      rewrite <- comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Y) _ _ _ (to (i j)) (from (i j))).
      rewrite (iso_to_from (i j)).
      rewrite fmap_id, id_right.
      reflexivity.
  - intros f g h [i [Hmi Hti]] [k [Hmk Htk]].
    exists (fun j => iso_compose (k j) (i j)).
    split; intros; simpl.
    + rewrite Hmi, Hmk.
      rewrite <- !comp_assoc.
      reflexivity.
    + rewrite Hti, Htk.
      rewrite <- comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Y) _ _ _ (to (k j)) (to (i j))).
      reflexivity.
Qed.

(*
   本节说明 Diagrams 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Did {C : Category} (X : DObj C) : DHom X X := {|
  dW := Id[didx X];
  dtau := {| transform := fun j => id[ddiag X j] |}
|}.

Program Definition Dcomp {C : Category} {X Y Z : DObj C}
  (f : DHom Y Z) (g : DHom X Y) : DHom X Z := {|
  dW := dW f ◯ dW g;
  dtau := {| transform :=
               fun j => transform[dtau g] j ∘ transform[dtau f] (dW g j) |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite (naturality (dtau g) x y f0).
  change (@fmap _ _ (ddiag Y ◯ dW g) x y f0)
    with (fmap[ddiag Y] (fmap[dW g] f0)).
  rewrite <- !comp_assoc.
  rewrite (naturality (dtau f) (dW g x) (dW g y) (fmap[dW g] f0)).
  change (@fmap _ _ (ddiag Z ◯ dW f) (dW g x) (dW g y) (fmap[dW g] f0))
    with (fmap[ddiag Z] (fmap[dW f] (fmap[dW g] f0))).
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  rewrite comp_assoc.
  rewrite (naturality (dtau g) x y f0).
  change (@fmap _ _ (ddiag Y ◯ dW g) x y f0)
    with (fmap[ddiag Y] (fmap[dW g] f0)).
  rewrite <- !comp_assoc.
  rewrite (naturality (dtau f) (dW g x) (dW g y) (fmap[dW g] f0)).
  change (@fmap _ _ (ddiag Z ◯ dW f) (dW g x) (dW g y) (fmap[dW g] f0))
    with (fmap[ddiag Z] (fmap[dW f] (fmap[dW g] f0))).
  reflexivity.
Qed.

Lemma Dcomp_respects {C : Category} {X Y Z : DObj C}
  (f f' : DHom Y Z) (Ef : DHom_equiv f f')
  (g g' : DHom X Y) (Eg : DHom_equiv g g') :
  DHom_equiv (Dcomp f g) (Dcomp f' g').
Proof.
  destruct Ef as [i [Hmi Hti]].
  destruct Eg as [k [Hmk Htk]].
  unshelve eexists.
  - intro j.
    exact (iso_compose (@fobj_iso _ _ (dW f') _ _ (k j)) (i (dW g j))).
  - split.
    + intros x y h; simpl.
      rewrite Hmi.
      rewrite Hmk.
      rewrite !fmap_comp.
      rewrite <- !comp_assoc.
      reflexivity.
    + intro j; simpl.
      rewrite Htk.
      rewrite Hti.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap[ddiag Y] (to (k j)))
                          (transform[dtau f'] (dW g j))
                          (fmap[ddiag Z] (to (i (dW g j))))).
      rewrite (naturality (dtau f') (dW g j) (dW g' j) (to (k j))).
      change (@fmap _ _ (ddiag Z ◯ dW f') (dW g j) (dW g' j) (to (k j)))
        with (fmap[ddiag Z] (fmap[dW f'] (to (k j)))).
      rewrite <- !comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Z) _ _ _
                    (fmap[dW f'] (to (k j))) (to (i (dW g j)))).
      reflexivity.
Qed.

Program Definition Diagrams (C : Category) : Category := {|
  obj := DObj C;
  hom := @DHom C;
  homset := @DHom_Setoid C;
  id := @Did C;
  compose := @Dcomp C
|}.
Next Obligation.
  intros f f' Ef g g' Eg.
  exact (Dcomp_respects f f' Ef g g' Eg).
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, !id_right.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_left, id_right.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_right, comp_assoc.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_right, comp_assoc.
Qed.

Example Diagrams_obj (C : Category) : obj[Diagrams C] = DObj C := eq_refl.

Example Diagrams_hom (C : Category) (X Y : Diagrams C) :
  (X ~{Diagrams C}~> Y) = DHom X Y := eq_refl.

(** ** The limit functor on the opposite of the category of diagrams *)

Section LimDiagrams.

Context {C : Category}.
Context (L : @Complete C).

Definition dlim (X : DObj C) : C :=
  vertex_obj[@limit_cone (didx X) C (ddiag X) (L (didx X) (ddiag X))].

Definition dlim_is (X : DObj C) : IsALimit (ddiag X) (dlim X) :=
  limit_is_alimit (L (didx X) (ddiag X)).

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition dlim_cone {X Y : DObj C} (f : DHom X Y) : Cone (ddiag X) :=
  cone_along (dtau f)
    (cone_reindex (dW f) (isalimit_cone (dlim_is Y))).

Example dlim_cone_apex {X Y : DObj C} (f : DHom X Y) :
  vertex_obj[dlim_cone f] = dlim Y := eq_refl.

(* The arrow part: the unique mediator into the limit of [ddiag X]. *)
Definition dlim_map {X Y : DObj C} (f : DHom X Y) : dlim Y ~{C}~> dlim X :=
  limit_med (dlim_is X) (dlim_cone f).

Lemma dlim_map_commutes {X Y : DObj C} (f : DHom X Y) (j : didx X) :
  limit_leg (dlim_is X) j ∘ dlim_map f
    ≈ transform[dtau f] j ∘ limit_leg (dlim_is Y) (dW f j).
Proof. exact (limit_med_commutes (dlim_is X) (dlim_cone f) j). Qed.

Lemma dlim_map_unique {X Y : DObj C} (f : DHom X Y)
  (v : dlim Y ~{C}~> dlim X) :
  (∀ j : didx X, limit_leg (dlim_is X) j ∘ v
                 ≈ transform[dtau f] j ∘ limit_leg (dlim_is Y) (dW f j)) →
  dlim_map f ≈ v.
Proof. intro Hv. exact (limit_med_unique (dlim_is X) (dlim_cone f) v Hv). Qed.

(* Mac Lane V.2 Exercise 5: over a complete target, taking limits is a
   functor on the opposite of the category of diagrams. *)
Program Definition LimDiagrams : (Diagrams C)^op ⟶ C := {|
  fobj := dlim;
  fmap := fun X Y f => dlim_map f
|}.
Next Obligation.
  intros f g [i [Hm Ht]].
  symmetry.
  apply dlim_map_unique; intro j.
  rewrite dlim_map_commutes.
  rewrite Ht.
  rewrite <- comp_assoc.
  rewrite (limit_leg_coherence (dlim_is x) (to (i j))).
  reflexivity.
Qed.
Next Obligation.
  apply dlim_map_unique; intro j.
  simpl.
  now rewrite id_left, id_right.
Qed.
Next Obligation.
  apply dlim_map_unique; intro j.
  simpl.
  rewrite comp_assoc.
  rewrite (dlim_map_commutes f j).
  rewrite <- comp_assoc.
  rewrite (dlim_map_commutes g (dW f j)).
  rewrite comp_assoc.
  reflexivity.
Qed.

Example LimDiagrams_fobj (X : DObj C) : LimDiagrams X = dlim X := eq_refl.

Example LimDiagrams_fmap {X Y : DObj C} (f : DHom X Y) :
  fmap[LimDiagrams] f = dlim_map f := eq_refl.

End LimDiagrams.

(** ** The colimit dual *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cocomplete_of_complete_op {C : Category} (L : @Complete (Opposite C)) :
  @Cocomplete C :=
  fun D F => L (Opposite D) (Opposite_Functor F).

Example cocomplete_roundtrip {C : Category} (L : @Cocomplete C) :
  cocomplete_of_complete_op (Complete_op_of_Cocomplete L) = L := eq_refl.

Example complete_op_roundtrip {C : Category} (L : @Complete (Opposite C)) :
  Complete_op_of_Cocomplete (cocomplete_of_complete_op L) = L := eq_refl.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ColimDiagrams {C : Category} (L : @Cocomplete C) :
  Diagrams (Opposite C) ⟶ C :=
  Opposite_Functor (LimDiagrams (Complete_op_of_Cocomplete L)).

Definition dcolim {C : Category} (L : @Cocomplete C) (X : DObj (Opposite C)) : C :=
  dlim (Complete_op_of_Cocomplete L) X.

Example ColimDiagrams_fobj {C : Category} (L : @Cocomplete C) (X : DObj (Opposite C)) :
  ColimDiagrams L X = dcolim L X := eq_refl.

(* At a diagram given as [F^op], the object part is the colimit apex the
   hypothesis chooses for [F]. *)
Example dcolim_is_colimit_apex {C : Category} (L : @Cocomplete C)
  {J : Category} (F : J ⟶ C) :
  dcolim L {| didx := Opposite J; ddiag := Opposite_Functor F |}
  = vertex_obj[@limit_cone (Opposite J) (Opposite C) (Opposite_Functor F) (L J F)]
  := eq_refl.

(** ** The comma form over Cat, and why it cannot carry the arrow part *)

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CommaDiagrams (C : Category) : Category :=
  @Comma Cat 1 Cat Id[Cat] (@Diagonal Cat 1 C).

Example CommaDiagrams_equiv (C : Category) (x y : CommaDiagrams C)
  (f g : x ~{CommaDiagrams C}~> y) :
  (f ≈ g) = ((fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g))%type := eq_refl.

(*
   本节说明 Diagrams 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition comma_diagrams_obj {C : Category} (x : CommaDiagrams C) : DObj C :=
  {| didx := fst `1 x; ddiag := `2 x |}.

Definition comma_diagrams_arrow {C : Category} {x y : CommaDiagrams C}
  (f : x ~{CommaDiagrams C}~> y) :
  DHom (comma_diagrams_obj x) (comma_diagrams_obj y).
Proof.
  unshelve refine (@Build_DHom C (comma_diagrams_obj x) (comma_diagrams_obj y) (fst `1 f)
                     (@Build_Transform _ _ (`2 y ◯ fst `1 f) (`2 x)
                        (fun j => to (`1 (`2 f) j)) _ _)).
  - intros a b h; simpl in *.
    pose proof (`2 (`2 f) a b h) as Hn; simpl in Hn.
    rewrite Hn.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
  - intros a b h; simpl in *.
    pose proof (`2 (`2 f) a b h) as Hn; simpl in Hn.
    rewrite Hn.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
Defined.

Example comma_diagrams_arrow_W {C : Category} {x y : CommaDiagrams C}
  (f : x ~{CommaDiagrams C}~> y) :
  dW (comma_diagrams_arrow f) = fst `1 f := eq_refl.

(** ** At a fixed shape, the arrow part is #353's [Lim_map] *)

Section FixedShape.

Context {C : Category} (L : @Complete C) {J : Category}.

(* A natural transformation [b : F ⟹ G] as an arrow (J, G) → (J, F) of
   [Diagrams C] with the identity shape functor. *)
Definition fixed_hom {F G : J ⟶ C} (b : F ⟹ G) :
  DHom {| didx := J; ddiag := G |} {| didx := J; ddiag := F |}.
Proof.
  unshelve refine (@Build_DHom C {| didx := J; ddiag := G |} {| didx := J; ddiag := F |}
                     Id[J] (@Build_Transform _ _ (F ◯ Id[J]) G (fun j => transform[b] j) _ _)).
  - intros; simpl. apply naturality.
  - intros; simpl. apply naturality_sym.
Defined.

Example lim_obj_is_dlim (F : J ⟶ C) :
  @lim_obj J C (Complete_HasLimitsOfShape L J) F = dlim L {| didx := J; ddiag := F |}
  := eq_refl.

(* Adjunction/Diagonal/Limit.v's fixed-shape limit functor is the restriction
   of [LimDiagrams] to the identity shape functor. *)
Lemma dlim_map_fixed {F G : J ⟶ C} (b : F ⟹ G) :
  dlim_map L (fixed_hom b) ≈ @Lim_map J C (Complete_HasLimitsOfShape L J) F G b.
Proof.
  apply dlim_map_unique; intro j.
  exact (@Lim_map_commutes J C (Complete_HasLimitsOfShape L J) F G b j).
Qed.

End FixedShape.
