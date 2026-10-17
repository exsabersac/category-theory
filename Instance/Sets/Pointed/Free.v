Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/pointed+set
 nLab:      https://ncatlab.org/nlab/show/free+functor
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Forgetful_functor
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book: Mac Lane, ibid., §III.1, Definition 1 (universal arrow),
 Book: Mac Lane, ibid., §IV.1, Theorem 2 (five equivalent
 Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Pointed_Forget : PointedSets ⟶ Sets := {|
  fobj := fun X => pointed_setoid X;
  fmap := fun _ _ f => pointed_map f
|}.
Next Obligation. intros X Y f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros X a; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z f g a; simpl; reflexivity. Qed.

#[export] Program Instance Pointed_Forget_Faithful : Faithful Pointed_Forget.
Next Obligation. intros X Y f g Hfg a; exact (Hfg a). Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreePointedObject (X : SetoidObject) : PointedSetoid := {|
  pointed_setoid := {| carrier := option (carrier X) |};
  pt := Datatypes.None
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_pointed_insert (X : SetoidObject) :
  X ~{Sets}~> Pointed_Forget (FreePointedObject X).
Proof.
  refine {| morphism := fun a => Datatypes.Some a |}.
Defined.

(** ** The universal property

    Every setoid map into the underlying setoid of a pointed set
    extends along the insertion to exactly one pointed map. *)

Section Extension.

Context {X : SetoidObject}.
Context {Y : PointedSetoid}.
Context (h : X ~{Sets}~> Pointed_Forget Y).

Definition fpt_ext_fun (o : carrier (FreePointedObject X)) : carrier Y :=
  match o with
  | Datatypes.Some a => h a
  | Datatypes.None   => pt Y
  end.

Program Definition fpt_ext_map :
  SetoidMorphism (pointed_setoid (FreePointedObject X))
                 (pointed_setoid Y) := {|
  morphism := fpt_ext_fun
|}.
Next Obligation.
  intros a b Hab.
  destruct a as [a|], b as [b|]; simpl in *; try contradiction.
  - now rewrite Hab.
  - reflexivity.
Qed.

(* The one law a pointed map owes, [preserves_pt], is [reflexivity]
   here: the mediator sends the adjoined point to [pt Y] by
   definition. *)
Definition free_pointed_extend : FreePointedObject X ~{PointedSets}~> Y.
Proof using X Y h.
  refine (Build_PointedMorphism (FreePointedObject X) Y fpt_ext_map _).
  simpl.
  reflexivity.
Defined.

Lemma free_pointed_extend_generators (a : carrier X) :
  free_pointed_extend (Datatypes.Some a) ≈ h a.
Proof. reflexivity. Qed.

(* Uniqueness: two cases, no induction.  The [Some] case is the
   hypothesis; the [None] case is the competitor's own [preserves_pt],
   since [None] IS the basepoint of the free object. *)
Lemma free_pointed_extend_unique
  (g : FreePointedObject X ~{PointedSets}~> Y)
  (Hg : ∀ a : carrier X, g (Datatypes.Some a) ≈ h a) :
  g ≈ free_pointed_extend.
Proof.
  intros [a|]; simpl.
  - exact (Hg a).
  - exact (preserves_pt g).
Qed.

End Extension.

Arguments fpt_ext_fun {X Y} h o.
Arguments fpt_ext_map {X Y} h.
Arguments free_pointed_extend {X Y} h.

(** The universal property in the shape [universal_arrow_from_UMP]
    consumes. *)

Theorem free_pointed_universal (X : SetoidObject) :
  ∀ (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y),
    ∃! g : FreePointedObject X ~{PointedSets}~> Y,
      h ≈ fmap[Pointed_Forget] g ∘ free_pointed_insert X.
Proof.
  intros Y h.
  unshelve eexists.
  - exact (free_pointed_extend h).
  - intro a; simpl.
    symmetry; exact (free_pointed_extend_generators h a).
  - intros g Hg o; simpl.
    symmetry; apply (free_pointed_extend_unique h g).
    intro a; symmetry; exact (Hg a).
Qed.

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_pointed_universal_arrow (X : Sets)
  : UniversalArrow X Pointed_Forget :=
  universal_arrow_from_UMP X Pointed_Forget (FreePointedObject X)
    (free_pointed_insert X) (free_pointed_universal X).

(** The same content in the direct encoding, where the universal object
    is named rather than projected out of a comma category. *)

Program Definition free_pointed_AUniversalArrow (X : Sets)
  : AUniversalArrow X Pointed_Forget (FreePointedObject X) := {|
  universal_arrow := free_pointed_insert X
|}.
Next Obligation.
  intros X Y h.
  unshelve eexists.
  - exact (free_pointed_extend h).
  - intro a; simpl.
    exact (free_pointed_extend_generators h a).
  - intros g Hg o; simpl.
    symmetry; apply (free_pointed_extend_unique h g).
    intro a; exact (Hg a).
Qed.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreePointed : Sets ⟶ PointedSets :=
  LeftAdjointFunctorFromUniversalArrows Pointed_Forget
    free_pointed_universal_arrow.

Definition free_pointed_adjunction : FreePointed ⊣ Pointed_Forget :=
  AdjunctionFromUniversalArrows Pointed_Forget free_pointed_universal_arrow.

(** ** Strengths, measured strict-first

    First the [eq_refl] identifications. *)

Example free_pointed_forget_obj (X : PointedSetoid) :
  Pointed_Forget X = pointed_setoid X := eq_refl.

Example free_pointed_carrier (X : SetoidObject) :
  carrier (FreePointedObject X) = option (carrier X) := eq_refl.

Example free_pointed_basepoint (X : SetoidObject) :
  pt (FreePointedObject X) = Datatypes.None := eq_refl.

Example free_pointed_insert_is_Some (X : SetoidObject) (a : carrier X) :
  free_pointed_insert X a = Datatypes.Some a := eq_refl.

Example free_pointed_extend_some_strict (X : SetoidObject)
  (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y) (a : carrier X) :
  free_pointed_extend h (Datatypes.Some a) = h a := eq_refl.

Example free_pointed_extend_none_strict (X : SetoidObject)
  (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y) :
  free_pointed_extend h Datatypes.None = pt Y := eq_refl.

(* [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. *)
Example free_pointed_arrow_is_insert (X : Sets) :
  @arrow _ _ X Pointed_Forget (free_pointed_universal_arrow X)
    = free_pointed_insert X := eq_refl.

Example FreePointed_obj (X : Sets) :
  FreePointed X = FreePointedObject X := eq_refl.

(** The unit.  [unit] is DERIVED in Theory/Adjunction.v (it is ⌊id⌋),
    not a field, so what it computes to has to be checked. *)

Definition free_pointed_unit (X : Sets)
  : X ~{Sets}~> Pointed_Forget (FreePointed X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_pointed_adjunction X.

Example free_pointed_unit_is_insert (X : Sets) (a : carrier X) :
  free_pointed_unit X a = Datatypes.Some a := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_pointed_transpose {X : Sets} {Y : PointedSets}
  (g : FreePointed X ~{PointedSets}~> Y) : X ~{Sets}~> Pointed_Forget Y :=
  fmap[Pointed_Forget] g ∘ free_pointed_insert X.

Example free_pointed_transpose_is_adj (X : Sets) (Y : PointedSets)
  (g : FreePointed X ~{PointedSets}~> Y) :
  to (@adj _ _ _ _ free_pointed_adjunction X Y) g
    = free_pointed_transpose g := eq_refl.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_pointed_from_adj (X : Sets) (Y : PointedSets)
  (h : X ~{Sets}~> Pointed_Forget Y) :
  from (@adj _ _ _ _ free_pointed_adjunction X Y) h
    ≈ free_pointed_extend h.
Proof.
  apply (free_pointed_extend_unique h).
  intro a.
  exact (@iso_to_from _ _ _ (@adj _ _ _ _ free_pointed_adjunction X Y) h a).
Qed.

(** Restriction to the generators is a bijection whose inverse is
    extension.  The first round trip is [reflexivity] at every
    generator. *)

Lemma free_pointed_transpose_extend {X : Sets} {Y : PointedSets}
  (h : X ~{Sets}~> Pointed_Forget Y) :
  free_pointed_transpose (free_pointed_extend h) ≈ h.
Proof. intro a; simpl; reflexivity. Qed.

Lemma free_pointed_extend_transpose {X : Sets} {Y : PointedSets}
  (g : FreePointed X ~{PointedSets}~> Y) :
  free_pointed_extend (free_pointed_transpose g) ≈ g.
Proof.
  intro o; simpl.
  symmetry; apply (free_pointed_extend_unique (free_pointed_transpose g) g).
  intro a; simpl; reflexivity.
Qed.

(** The counit.  It is the OTHER transpose, ⌈id⌉, so it does not
    compute; what is proved is that it is the identity away from the
    adjoined point and sends that point to the basepoint. *)

Definition free_pointed_counit (Y : PointedSets)
  : FreePointed (Pointed_Forget Y) ~{PointedSets}~> Y :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_pointed_adjunction Y.

Lemma free_pointed_counit_evaluates (Y : PointedSets)
  (o : carrier (Pointed_Forget Y)) :
  free_pointed_counit Y (Datatypes.Some o) ≈ o.
Proof.
  exact (free_pointed_from_adj (Pointed_Forget Y) Y id{Sets}
           (Datatypes.Some o)).
Qed.

Lemma free_pointed_counit_kills_point (Y : PointedSets) :
  free_pointed_counit Y Datatypes.None ≈ pt Y.
Proof. exact (preserves_pt (free_pointed_counit Y)). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example free_pointed_fmap_is_from_adj (X Y : Sets) (u : X ~{Sets}~> Y) :
  fmap[FreePointed] u
    = from (@adj _ _ _ _ free_pointed_adjunction X (FreePointed Y))
        (free_pointed_insert Y ∘ u) := eq_refl.

Lemma free_pointed_fmap_some (X Y : Sets) (u : X ~{Sets}~> Y)
  (a : carrier X) :
  fmap[FreePointed] u (Datatypes.Some a) ≈ Datatypes.Some (u a).
Proof.
  exact (free_pointed_from_adj X (FreePointed Y)
           (free_pointed_insert Y ∘ u) (Datatypes.Some a)).
Qed.

Lemma free_pointed_fmap_none (X Y : Sets) (u : X ~{Sets}~> Y) :
  fmap[FreePointed] u Datatypes.None ≈ Datatypes.None.
Proof. exact (preserves_pt (fmap[FreePointed] u)). Qed.

(** ** Naturality, in Mac Lane's §IV.1 shape

    The two clauses are the adjunction class's own fields, restated in
    the transpose's vocabulary. *)

Lemma free_pointed_naturality_in_set {X Y : Sets} {Z : PointedSets}
  (g : FreePointed Y ~{PointedSets}~> Z) (u : X ~{Sets}~> Y) :
  free_pointed_transpose (g ∘ fmap[FreePointed] u)
    ≈ free_pointed_transpose g ∘ u.
Proof. exact (@to_adj_nat_l _ _ _ _ free_pointed_adjunction X Y Z g u). Qed.

Lemma free_pointed_naturality_in_pointed {X : Sets} {Y Z : PointedSets}
  (k : Y ~{PointedSets}~> Z) (g : FreePointed X ~{PointedSets}~> Y) :
  free_pointed_transpose (k ∘ g)
    ≈ fmap[Pointed_Forget] k ∘ free_pointed_transpose g.
Proof. exact (@to_adj_nat_r _ _ _ _ free_pointed_adjunction X Y Z k g). Qed.

(** The triangle identities, inherited. *)

Corollary free_pointed_triangle_left (X : Sets) :
  free_pointed_counit (FreePointed X)
    ∘ fmap[FreePointed] (free_pointed_unit X) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ free_pointed_adjunction X). Qed.

Corollary free_pointed_triangle_right (Y : PointedSets) :
  fmap[Pointed_Forget] (free_pointed_counit Y)
    ∘ free_pointed_unit (Pointed_Forget Y) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ free_pointed_adjunction Y). Qed.

(* The composite [Pointed_Forget ◯ FreePointed] has object action
   [option].  No monad is built; see the header. *)
Example free_pointed_maybe_carrier (X : Sets) :
  carrier (Pointed_Forget (FreePointed X)) = option (carrier X) := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem free_pointed_point_is_new (X : SetoidObject) (a : carrier X) :
  free_pointed_insert X a ≈ pt (FreePointedObject X) → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_insert_injective (X : SetoidObject)
  (a b : carrier X) :
  free_pointed_insert X a ≈ free_pointed_insert X b → a ≈ b.
Proof. exact (fun H => H). Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fpt_one : SetoidObject := {| carrier := poly_unit |}.

Definition fpt_two : SetoidObject := {| carrier := option poly_unit |}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example PointedTwo_is_free_on_one :
  FreePointedObject fpt_one = PointedTwo := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fpt_gen1 : carrier (FreePointedObject fpt_two) :=
  Datatypes.Some (Datatypes.Some ttt).

Definition fpt_gen2 : carrier (FreePointedObject fpt_two) :=
  Datatypes.Some Datatypes.None.

Theorem free_pointed_two_has_three_elements
  (o : carrier (FreePointedObject fpt_two)) :
  ((o = fpt_gen1) + (o = fpt_gen2)) + (o = pt (FreePointedObject fpt_two)).
Proof.
  destruct o as [[u|]|].
  - destruct u; left; left; reflexivity.
  - left; right; reflexivity.
  - right; reflexivity.
Qed.

Theorem free_pointed_two_generators_distinct : fpt_gen1 ≈ fpt_gen2 → False.
Proof. exact (fun H => H). Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fpt_probe_id : fpt_two ~{Sets}~> Pointed_Forget PointedTwo :=
  id{Sets}.

Definition fpt_probe_const : fpt_two ~{Sets}~> Pointed_Forget PointedTwo.
Proof.
  refine {| morphism := fun _ => Datatypes.Some ttt |}.
  exact (fun _ _ _ => reflexivity (Datatypes.Some ttt)).
Defined.

(** The mediator computes, at Leibniz equality, on every element. *)

Example fpt_probe_id_gen1 :
  free_pointed_extend fpt_probe_id fpt_gen1 = Datatypes.Some ttt := eq_refl.

Example fpt_probe_id_gen2 :
  free_pointed_extend fpt_probe_id fpt_gen2 = Datatypes.None := eq_refl.

Example fpt_probe_id_point :
  free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two))
    = Datatypes.None := eq_refl.

Example fpt_probe_const_gen2 :
  free_pointed_extend fpt_probe_const fpt_gen2 = Datatypes.Some ttt
  := eq_refl.

Example fpt_probe_const_point :
  free_pointed_extend fpt_probe_const (pt (FreePointedObject fpt_two))
    = Datatypes.None := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem free_pointed_gen1_gen2_separated_out :
  free_pointed_extend fpt_probe_id fpt_gen1
    ≈ free_pointed_extend fpt_probe_id fpt_gen2 → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_gen1_point_separated_out :
  free_pointed_extend fpt_probe_id fpt_gen1
    ≈ free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two))
    → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_gen2_point_separated_out :
  free_pointed_extend fpt_probe_const fpt_gen2
    ≈ free_pointed_extend fpt_probe_const (pt (FreePointedObject fpt_two))
    → False.
Proof. exact (fun H => H). Qed.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem free_pointed_extend_id_collapses :
  free_pointed_extend fpt_probe_id fpt_gen2
    ≈ free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two)).
Proof. reflexivity. Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition free_pointed_instrument_check :
  Datatypes.true = Datatypes.false := eq_refl.

Fail Example free_pointed_from_adj_is_not_strict
  (X : Sets) (Y : PointedSets) (h : X ~{Sets}~> Pointed_Forget Y) :
  from (@adj _ _ _ _ free_pointed_adjunction X Y) h
    = free_pointed_extend h := eq_refl.

Fail Example free_pointed_counit_is_not_strict
  (Y : PointedSets) (o : carrier (Pointed_Forget Y)) :
  free_pointed_counit Y (Datatypes.Some o) = o := eq_refl.

Fail Example free_pointed_fmap_is_not_strict
  (X Y : Sets) (u : X ~{Sets}~> Y) (a : carrier X) :
  fmap[FreePointed] u (Datatypes.Some a) = Datatypes.Some (u a) := eq_refl.
