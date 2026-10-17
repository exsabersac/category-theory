Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.

Generalizable All Variables.

(** * The disjoint union is the coproduct in Top *)

(*
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 Wikipedia: https://en.wikipedia.org/wiki/Disjoint_union_(topology)

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The disjoint union of two spaces *)

Section SumTop.

Context (X Y : TopSpace).

(* The points: the sum of the two point sets, under Lib/Datatypes.v's
   [sum_setoid], which never identifies across the summands. *)
Definition sum_carrier : SetoidObject := {|
  carrier := (carrier (top_carrier X) + carrier (top_carrier Y))%type;
  is_setoid := sum_setoid
|}.

(* A subset of the sum is open exactly when both of its restrictions
   are — Awodey's O(X + Y) ≅ O(X) × O(Y), taken as the definition. *)
Definition sum_open (W : sum_carrier → Type) : Type :=
  (IsOpen X (fun x => W (Datatypes.inl x))
     ∧ IsOpen Y (fun y => W (Datatypes.inr y)))%type.

Lemma sum_respects (U V : sum_carrier → Type) :
  (∀ u, U u ↔ V u) → sum_open U → sum_open V.
Proof.
  intros H [HX HY].
  split.
  - exact (open_respects X _ _ (fun x => H (Datatypes.inl x)) HX).
  - exact (open_respects Y _ _ (fun y => H (Datatypes.inr y)) HY).
Qed.

(* Respect for the points' own equality: equivalent points of the sum lie
   in the same summand, so each case is that summand's [open_proper]. *)
Lemma sum_proper (W : sum_carrier → Type) :
  sum_open W → ∀ u v : sum_carrier, u ≈ v → W u → W v.
Proof.
  intros [HX HY] [a|a] [b|b] Huv Wu; simpl in Huv.
  - exact (open_proper X _ HX a b Huv Wu).
  - contradiction.
  - contradiction.
  - exact (open_proper Y _ HY a b Huv Wu).
Qed.

Lemma sum_union (I : Type) (U : I → (sum_carrier → Type)) :
  (∀ i, sum_open (U i)) → sum_open (fun u => { i : I & U i u }).
Proof.
  intro H.
  split.
  - exact (open_union X I (fun i x => U i (Datatypes.inl x))
             (fun i => fst (H i))).
  - exact (open_union Y I (fun i y => U i (Datatypes.inr y))
             (fun i => snd (H i))).
Qed.

Lemma sum_whole : sum_open (fun _ => poly_unit).
Proof. exact (open_whole X, open_whole Y). Qed.

Lemma sum_inter (U V : sum_carrier → Type) :
  sum_open U → sum_open V → sum_open (fun u => U u ∧ V u).
Proof.
  intros [HXU HYU] [HXV HYV].
  split.
  - exact (open_inter X _ _ HXU HXV).
  - exact (open_inter Y _ _ HYU HYV).
Qed.

Definition Sum_Top : TopSpace := {|
  top_carrier   := sum_carrier;
  IsOpen        := sum_open;
  open_respects := sum_respects;
  open_proper   := sum_proper;
  open_union    := sum_union;
  open_whole    := sum_whole;
  open_inter    := sum_inter
|}.

(** ** The injections *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sum_inl_map : SetoidMorphism (top_carrier X) sum_carrier.
Proof.
  unshelve notypeclasses refine {| morphism := Datatypes.inl |}.
  intros u v Huv; exact Huv.
Defined.

Definition sum_inr_map : SetoidMorphism (top_carrier Y) sum_carrier.
Proof.
  unshelve notypeclasses refine {| morphism := Datatypes.inr |}.
  intros u v Huv; exact Huv.
Defined.

(* Named constructor rather than a [{| … |}] literal: the record's index
   [Y] would otherwise be inferred from [continuous_map]'s type before the
   ascription has forced it to [Sum_Top]. *)
Definition Top_inl : X ~{Top}~> Sum_Top :=
  Build_ContinuousMorphism X Sum_Top sum_inl_map (fun W HW => fst HW).

Definition Top_inr : Y ~{Top}~> Sum_Top :=
  Build_ContinuousMorphism Y Sum_Top sum_inr_map (fun W HW => snd HW).

End SumTop.

Arguments sum_open {X Y} W.

(** ** The copairing *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sum_merge_map {X Y Z : TopSpace}
  (f : X ~{Top}~> Z) (g : Y ~{Top}~> Z) :
  SetoidMorphism (sum_carrier X Y) (top_carrier Z).
Proof.
  unshelve notypeclasses refine {| morphism := fun u =>
              match u with
              | Datatypes.inl a => continuous_map f a
              | Datatypes.inr b => continuous_map g b
              end |}.
  intros [a|a] [b|b] H; simpl in H; try contradiction.
  - exact (proper_morphism (continuous_map f) a b H).
  - exact (proper_morphism (continuous_map g) a b H).
Defined.

(* Continuity is exactly the pair of the two continuities: the preimage's
   two restrictions ARE the preimages under f and under g. *)
Definition Top_merge {X Y Z : TopSpace}
  (f : X ~{Top}~> Z) (g : Y ~{Top}~> Z) : Sum_Top X Y ~{Top}~> Z :=
  Build_ContinuousMorphism (Sum_Top X Y) Z (sum_merge_map f g)
    (fun W HW => (continuity f W HW, continuity g W HW)).

(** ** The universal property *)

Lemma Top_sum_ump {X Y Z : TopSpace}
      (f : X ~{Top}~> Z) (g : Y ~{Top}~> Z)
      (h : Sum_Top X Y ~{Top}~> Z) :
  h ≈ Top_merge f g
    ↔ (h ∘ Top_inl X Y ≈ f) ∧ (h ∘ Top_inr X Y ≈ g).
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

Lemma Top_merge_respects (X Y Z : TopSpace) :
  Proper (equiv ==> equiv ==> equiv) (@Top_merge X Y Z).
Proof.
  intros f f' Hf g g' Hg [a|a].
  - exact (Hf a).
  - exact (Hg a).
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Top_cofork (Z X Y : TopSpace)
  (f : X ~{Top}~> Z) (g : Y ~{Top}~> Z) : Sum_Top X Y ~{Top}~> Z :=
  Top_merge f g.

Lemma Top_cofork_respects (Z X Y : TopSpace) :
  Proper (equiv ==> equiv ==> equiv) (Top_cofork Z X Y).
Proof. exact (Top_merge_respects X Y Z). Qed.

Lemma Top_cofork_ump (Z X Y : TopSpace)
      (f : X ~{Top}~> Z) (g : Y ~{Top}~> Z)
      (h : Sum_Top X Y ~{Top}~> Z) :
  h ≈ Top_cofork Z X Y f g
    ↔ (h ∘ Top_inl X Y ≈ f) ∧ (h ∘ Top_inr X Y ≈ g).
Proof. exact (Top_sum_ump f g h). Qed.

(* [Cocartesian Top] is [@Cartesian (Top^op)]; the constructor and its
   category are named explicitly for the orientation reason recorded in
   Structure/Biproduct/Cartesian.v. *)
#[export] Instance Top_Cocartesian : @Cocartesian Top :=
  @Build_Cartesian (Top^op)
    Sum_Top
    Top_cofork
    Top_inl
    Top_inr
    Top_cofork_respects
    Top_cofork_ump.

(** ** Strict identifications *)

Example Top_coprod_obj (X Y : TopSpace) :
  @Coprod Top Top_Cocartesian X Y = Sum_Top X Y := eq_refl.

Example Top_coprod_carrier (X Y : TopSpace) :
  carrier (top_carrier (@Coprod Top Top_Cocartesian X Y))
    = (carrier (top_carrier X) + carrier (top_carrier Y))%type := eq_refl.

Example Top_inl_is_inl (X Y : TopSpace) :
  @inl Top Top_Cocartesian X Y = Top_inl X Y := eq_refl.

Example Top_inr_is_inr (X Y : TopSpace) :
  @inr Top Top_Cocartesian X Y = Top_inr X Y := eq_refl.

Example Top_merge_is_merge (X Y Z : TopSpace)
  (f : X ~{Top}~> Z) (g : Y ~{Top}~> Z) :
  @merge Top Top_Cocartesian Z X Y f g = Top_merge f g := eq_refl.

(* Awodey's O(X + Y) ≅ O(X) × O(Y): here an identity of the two
   predicates, not an isomorphism of lattices. *)
Example sum_open_is_pair (X Y : TopSpace)
  (W : sum_carrier X Y → Type) :
  IsOpen (Sum_Top X Y) W
    = (IsOpen X (fun x => W (Datatypes.inl x))
         ∧ IsOpen Y (fun y => W (Datatypes.inr y)))%type := eq_refl.

(** ** The empty space is the unit, and the symmetry and associativity *)

(* Free from Structure/Cocartesian.v once Instance/Top.v's [Top_Initial]
   is in scope. *)
Example Top_coprod_empty_left (X : TopSpace) :
  @Isomorphism Top (Sum_Top Empty_Top X) X :=
  @coprod_zero_l Top Top_Cocartesian Top_Initial X.

Example Top_coprod_empty_right (X : TopSpace) :
  @Isomorphism Top (Sum_Top X Empty_Top) X :=
  @coprod_zero_r Top Top_Cocartesian Top_Initial X.

Example Top_coprod_comm (X Y : TopSpace) :
  @Isomorphism Top (Sum_Top X Y) (Sum_Top Y X) :=
  @coprod_comm Top Top_Cocartesian X Y.

Example Top_coprod_assoc (X Y Z : TopSpace) :
  @Isomorphism Top (Sum_Top (Sum_Top X Y) Z) (Sum_Top X (Sum_Top Y Z)) :=
  @coprod_assoc Top Top_Cocartesian X Y Z.

(** ** The disjoint union of discrete spaces is discrete *)

(* Stated as a biconditional between the two openness predicates, so the
   two topologies are identified on the nose rather than through a
   comparison map. *)
Theorem sum_of_discrete (A B : SetoidObject)
        (W : sum_carrier (Discrete_Top A) (Discrete_Top B) → Type) :
  IsOpen (Sum_Top (Discrete_Top A) (Discrete_Top B)) W
    ↔ (∀ u v : sum_carrier (Discrete_Top A) (Discrete_Top B),
          u ≈ v → W u → W v).
Proof.
  split.
  - intros HW u v Huv Wu.
    exact (sum_proper (Discrete_Top A) (Discrete_Top B) W HW u v Huv Wu).
  - intro H.
    split.
    + intros a b Hab Wa.
      exact (H (Datatypes.inl a) (Datatypes.inl b) Hab Wa).
    + intros a b Hab Wa.
      exact (H (Datatypes.inr a) (Datatypes.inr b) Hab Wa).
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary point_sum_discrete
        (W : sum_carrier Point_Top Point_Top → Type) :
  IsOpen (Sum_Top Point_Top Point_Top) W
    ↔ (∀ u v : sum_carrier Point_Top Point_Top, u ≈ v → W u → W v).
Proof. exact (sum_of_discrete _ _ W). Qed.

(** ** Non-vacuity *)

(* The two injections of [1 + 1] land on different points: the singleton
   subset of the left copy is a subset that one hits and the other does
   not.  So the coproduct does not collapse. *)
Definition left_point (u : sum_carrier Point_Top Point_Top) : Type :=
  match u with
  | Datatypes.inl _ => poly_unit
  | Datatypes.inr _ => False
  end.

(* It is open, which is what makes the two copies topologically distinct
   and not merely set-theoretically so. *)
Lemma left_point_open : IsOpen (Sum_Top Point_Top Point_Top) left_point.
Proof.
  split.
  - exact (open_whole Point_Top).
  - exact (open_empty Point_Top).
Qed.

Lemma point_sum_injections_differ :
  continuous_map (Top_inl Point_Top Point_Top) ttt
    ≈ continuous_map (Top_inr Point_Top Point_Top) ttt → False.
Proof. exact (fun H => H). Qed.
