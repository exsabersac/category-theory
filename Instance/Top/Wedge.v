Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 Wikipedia: https://en.wikipedia.org/wiki/Wedge_sum

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The glued carrier *)

Section WedgeSum.

Context (X Y : PointedTop).

Definition wpoint : Type :=
  (carrier (top_carrier (ptop_space X))
     + carrier (top_carrier (ptop_space Y)))%type.

(* 相关说明。 （已译） *)
Definition wedge_rel (u v : wpoint) : Type :=
  match u, v with
  | Datatypes.inl a, Datatypes.inl a' => a ≈ a'
  | Datatypes.inr b, Datatypes.inr b' => b ≈ b'
  | Datatypes.inl a, Datatypes.inr b' =>
      ((a ≈ ptop_pt X) ∧ (b' ≈ ptop_pt Y))%type
  | Datatypes.inr b, Datatypes.inl a' =>
      ((b ≈ ptop_pt Y) ∧ (a' ≈ ptop_pt X))%type
  end.

Lemma wedge_rel_Equivalence : Equivalence wedge_rel.
Proof.
  constructor.
  - intros [a|a]; simpl; reflexivity.
  - intros [a|a] [b|b] H; simpl in *.
    + now symmetry.
    + exact (snd H, fst H).
    + exact (snd H, fst H).
    + now symmetry.
  - intros [a|a] [b|b] [c|c] H1 H2; simpl in *.
    + now transitivity b.
    + exact (transitivity H1 (fst H2), snd H2).
    + transitivity (ptop_pt X);
        [ exact (fst H1) | symmetry; exact (snd H2) ].
    + exact (fst H1, transitivity (symmetry H2) (snd H1)).
    + exact (fst H1, transitivity (symmetry H2) (snd H1)).
    + transitivity (ptop_pt Y);
        [ exact (fst H1) | symmetry; exact (snd H2) ].
    + exact (transitivity H1 (fst H2), snd H2).
    + now transitivity b.
Qed.

Definition wedge_setoid : Setoid wpoint := {|
  equiv := wedge_rel;
  setoid_equiv := wedge_rel_Equivalence
|}.

Definition wedge_carrier : SetoidObject := {|
  carrier := wpoint;
  is_setoid := wedge_setoid
|}.

(** ** The quotient topology *)

(* 相关说明。 （已译） *)
Definition wedge_open (W : wedge_carrier → Type) : Type :=
  ((∀ u v : wedge_carrier, wedge_rel u v → W u → W v)
     ∧ IsOpen (ptop_space X) (fun a => W (Datatypes.inl a))
     ∧ IsOpen (ptop_space Y) (fun b => W (Datatypes.inr b)))%type.

Lemma wedge_respects (U V : wedge_carrier → Type) :
  (∀ u, U u ↔ V u) → wedge_open U → wedge_open V.
Proof.
  intros H [HR [HX HY]].
  split; [| split ].
  - intros u v Huv Vu.
    exact (fst (H v) (HR u v Huv (snd (H u) Vu))).
  - exact (open_respects (ptop_space X) _ _
             (fun a => H (Datatypes.inl a)) HX).
  - exact (open_respects (ptop_space Y) _ _
             (fun b => H (Datatypes.inr b)) HY).
Qed.

Lemma wedge_proper (W : wedge_carrier → Type) :
  wedge_open W → ∀ u v : wedge_carrier, u ≈ v → W u → W v.
Proof. intros [HR _] u v Huv Wu; exact (HR u v Huv Wu). Qed.

Lemma wedge_union (I : Type) (U : I → (wedge_carrier → Type)) :
  (∀ i, wedge_open (U i)) → wedge_open (fun u => { i : I & U i u }).
Proof.
  intro H.
  split; [| split ].
  - intros u v Huv [i Hi].
    exact (i; fst (H i) u v Huv Hi).
  - exact (open_union (ptop_space X) I
             (fun i a => U i (Datatypes.inl a))
             (fun i => fst (snd (H i)))).
  - exact (open_union (ptop_space Y) I
             (fun i b => U i (Datatypes.inr b))
             (fun i => snd (snd (H i)))).
Qed.

Lemma wedge_whole : wedge_open (fun _ => poly_unit).
Proof.
  split; [| split ].
  - intros u v _ _; exact ttt.
  - exact (open_whole (ptop_space X)).
  - exact (open_whole (ptop_space Y)).
Qed.

Lemma wedge_inter (U V : wedge_carrier → Type) :
  wedge_open U → wedge_open V → wedge_open (fun u => U u ∧ V u).
Proof.
  intros [HRU [HXU HYU]] [HRV [HXV HYV]].
  split; [| split ].
  - intros u v Huv [Uu Vu].
    exact (HRU u v Huv Uu, HRV u v Huv Vu).
  - exact (open_inter (ptop_space X) _ _ HXU HXV).
  - exact (open_inter (ptop_space Y) _ _ HYU HYV).
Qed.

Definition Wedge_Top : TopSpace := {|
  top_carrier   := wedge_carrier;
  IsOpen        := wedge_open;
  open_respects := wedge_respects;
  open_proper   := wedge_proper;
  open_union    := wedge_union;
  open_whole    := wedge_whole;
  open_inter    := wedge_inter
|}.

Definition WedgeSum : PointedTop := {|
  ptop_space := Wedge_Top;
  ptop_pt := Datatypes.inl (ptop_pt X)
|}.

(** ** The injections *)

Definition wedge_inl_map :
  SetoidMorphism (top_carrier (ptop_space X)) wedge_carrier.
Proof.
  unshelve notypeclasses refine {| morphism := Datatypes.inl |}.
  intros u v Huv; exact Huv.
Defined.

Definition wedge_inr_map :
  SetoidMorphism (top_carrier (ptop_space Y)) wedge_carrier.
Proof.
  unshelve notypeclasses refine {| morphism := Datatypes.inr |}.
  intros u v Huv; exact Huv.
Defined.

Definition wedge_inl_cont : ptop_space X ~{Top}~> Wedge_Top :=
  Build_ContinuousMorphism (ptop_space X) Wedge_Top wedge_inl_map
    (fun W HW => fst (snd HW)).

Definition wedge_inr_cont : ptop_space Y ~{Top}~> Wedge_Top :=
  Build_ContinuousMorphism (ptop_space Y) Wedge_Top wedge_inr_map
    (fun W HW => snd (snd HW)).

(* 相关说明。 （已译） *)
Definition Wedge_inl : X ~{Top_pointed}~> WedgeSum :=
  Build_PointedMap X WedgeSum wedge_inl_cont (reflexivity _).

Lemma wedge_inr_preserves :
  wedge_inr_cont (ptop_pt Y) ≈ ptop_pt WedgeSum.
Proof. exact (reflexivity _, reflexivity _). Qed.

Definition Wedge_inr : Y ~{Top_pointed}~> WedgeSum :=
  Build_PointedMap Y WedgeSum wedge_inr_cont wedge_inr_preserves.

End WedgeSum.

Arguments wedge_rel {X Y} u v.
Arguments wedge_open {X Y} W.

(** ** The copairing *)

(*
   本节说明 Wedge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wedge_merge_map {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  SetoidMorphism (wedge_carrier X Y) (top_carrier (ptop_space Z)).
Proof.
  unshelve notypeclasses refine {| morphism := fun u =>
    match u with
    | Datatypes.inl a => ptop_map f a
    | Datatypes.inr b => ptop_map g b
    end |}.
  intros [a|a] [b|b] H; simpl in H.
  - exact (proper_morphism (continuous_map (ptop_map f)) a b H).
  - transitivity (ptop_pt Z).
    + transitivity (ptop_map f (ptop_pt X)).
      * exact (proper_morphism (continuous_map (ptop_map f)) _ _ (fst H)).
      * exact (ptop_preserves f).
    + transitivity (ptop_map g (ptop_pt Y)).
      * symmetry; exact (ptop_preserves g).
      * symmetry.
        exact (proper_morphism (continuous_map (ptop_map g)) _ _ (snd H)).
  - transitivity (ptop_pt Z).
    + transitivity (ptop_map g (ptop_pt Y)).
      * exact (proper_morphism (continuous_map (ptop_map g)) _ _ (fst H)).
      * exact (ptop_preserves g).
    + transitivity (ptop_map f (ptop_pt X)).
      * symmetry; exact (ptop_preserves f).
      * symmetry.
        exact (proper_morphism (continuous_map (ptop_map f)) _ _ (snd H)).
  - exact (proper_morphism (continuous_map (ptop_map g)) a b H).
Defined.

Lemma wedge_merge_cont {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  Continuous (Wedge_Top X Y) (ptop_space Z) (wedge_merge_map f g).
Proof.
  intros W HW.
  split; [| split ].
  - intros u v Huv Wu.
    exact (open_proper (ptop_space Z) W HW _ _
             (proper_morphism (wedge_merge_map f g) u v Huv) Wu).
  - exact (continuity (ptop_map f) W HW).
  - exact (continuity (ptop_map g) W HW).
Qed.

Definition wedge_merge_top {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  Wedge_Top X Y ~{Top}~> ptop_space Z :=
  Build_ContinuousMorphism (Wedge_Top X Y) (ptop_space Z)
    (wedge_merge_map f g) (wedge_merge_cont f g).

Definition Wedge_merge {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  WedgeSum X Y ~{Top_pointed}~> Z :=
  Build_PointedMap (WedgeSum X Y) Z (wedge_merge_top f g) (ptop_preserves f).

(** ** The universal property *)

Lemma Wedge_ump {X Y Z : PointedTop}
      (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z)
      (h : WedgeSum X Y ~{Top_pointed}~> Z) :
  h ≈ Wedge_merge f g
    ↔ (h ∘ Wedge_inl X Y ≈ f) ∧ (h ∘ Wedge_inr X Y ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + intro a; exact (Hh (Datatypes.inl a)).
    + intro b; exact (Hh (Datatypes.inr b)).
  - intros [Hl Hr] [a|a].
    + exact (Hl a).
    + exact (Hr a).
Qed.

(* 相关说明。 （已译） *)
Definition Wedge_cofork (Z X Y : PointedTop)
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  WedgeSum X Y ~{Top_pointed}~> Z := Wedge_merge f g.

Lemma Wedge_cofork_respects (Z X Y : PointedTop) :
  Proper (equiv ==> equiv ==> equiv) (Wedge_cofork Z X Y).
Proof.
  intros f f' Hf g g' Hg [a|a].
  - exact (Hf a).
  - exact (Hg a).
Qed.

Lemma Wedge_cofork_ump (Z X Y : PointedTop)
      (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z)
      (h : WedgeSum X Y ~{Top_pointed}~> Z) :
  h ≈ Wedge_cofork Z X Y f g
    ↔ (h ∘ Wedge_inl X Y ≈ f) ∧ (h ∘ Wedge_inr X Y ≈ g).
Proof. exact (Wedge_ump f g h). Qed.

#[export] Instance Top_pointed_Cocartesian : @Cocartesian Top_pointed :=
  @Build_Cartesian (Top_pointed^op)
    WedgeSum
    Wedge_cofork
    Wedge_inl
    Wedge_inr
    Wedge_cofork_respects
    Wedge_cofork_ump.

(** ** Strict identifications *)

Example Wedge_coprod_obj (X Y : PointedTop) :
  @Coprod Top_pointed Top_pointed_Cocartesian X Y = WedgeSum X Y := eq_refl.

Example Wedge_carrier_eq (X Y : PointedTop) :
  carrier (top_carrier (ptop_space
    (@Coprod Top_pointed Top_pointed_Cocartesian X Y)))
    = wpoint X Y := eq_refl.

Example Wedge_inl_is_inl (X Y : PointedTop) :
  @inl Top_pointed Top_pointed_Cocartesian X Y = Wedge_inl X Y := eq_refl.

Example Wedge_inr_is_inr (X Y : PointedTop) :
  @inr Top_pointed Top_pointed_Cocartesian X Y = Wedge_inr X Y := eq_refl.

Example Wedge_merge_is_merge (X Y Z : PointedTop)
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  @merge Top_pointed Top_pointed_Cocartesian Z X Y f g = Wedge_merge f g :=
  eq_refl.

(* 相关说明。 （已译） *)
Example Wedge_basepoint (X Y : PointedTop) :
  ptop_pt (@Coprod Top_pointed Top_pointed_Cocartesian X Y)
    = Datatypes.inl (ptop_pt X) := eq_refl.

(* Symmetry associativity come free cocartesian structure;
 unit laws do not, there being no 始对象 [Top_pointed]
 tree. （已译） *)
Example Wedge_comm (X Y : PointedTop) :
  @Isomorphism Top_pointed (WedgeSum X Y) (WedgeSum Y X) :=
  @coprod_comm Top_pointed Top_pointed_Cocartesian X Y.

Example Wedge_assoc (X Y Z : PointedTop) :
  @Isomorphism Top_pointed
    (WedgeSum (WedgeSum X Y) Z) (WedgeSum X (WedgeSum Y Z)) :=
  @coprod_assoc Top_pointed Top_pointed_Cocartesian X Y Z.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Lemma wedge_basepoints_identified (X Y : PointedTop) :
  continuous_map (ptop_map (Wedge_inl X Y)) (ptop_pt X)
    ≈ continuous_map (ptop_map (Wedge_inr X Y)) (ptop_pt Y).
Proof. exact (reflexivity _, reflexivity _). Qed.

(*
   本节说明 Wedge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wedge_is_not_sum (X Y : PointedTop) :
  continuous_map (Top_inl (ptop_space X) (ptop_space Y)) (ptop_pt X)
    ≈ continuous_map (Top_inr (ptop_space X) (ptop_space Y)) (ptop_pt Y)
  → False.
Proof. exact (fun H => H). Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition TwoPt : PointedTop := {|
  ptop_space := Sum_Top Point_Top Point_Top;
  ptop_pt := Datatypes.inl ttt
|}.

(* The two non-basepoint points of [TwoPt ∨ TwoPt] stay apart. *)
Lemma wedge_non_basepoints_differ :
  @wedge_rel TwoPt TwoPt
    (Datatypes.inl (Datatypes.inr ttt))
    (Datatypes.inr (Datatypes.inr ttt))
  → False.
Proof. exact (fun H => fst H). Qed.

(* 相关说明。 （已译） *)
Example wedge_two_pt_basepoints :
  @wedge_rel TwoPt TwoPt
    (Datatypes.inl (Datatypes.inl ttt))
    (Datatypes.inr (Datatypes.inl ttt)) :=
  (reflexivity _, reflexivity _).
