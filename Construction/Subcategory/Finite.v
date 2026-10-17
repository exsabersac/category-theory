Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * The finite setoids inside [Sets]: a worked full-subcategory example *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_finite_sets
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,

   本文件给出有限情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Finiteness of a setoid *)

(* Membership up to the ambient `≈` rather than up to `=`; `∨` is
   Category.Lib's `sum`, so this is `Type`-valued and can be eliminated into
   `Type`. *)
Fixpoint mem_upto {X : SetoidObject} (a : carrier X)
         (l : list (carrier X)) : Type :=
  match l with
  | nil       => False
  | cons b l' => (a ≈ b) ∨ mem_upto a l'
  end.

(* A setoid is finite when some list of its carrier exhausts it up to `≈`. *)
Definition FiniteSetoid (X : SetoidObject) : Type :=
  { l : list (carrier X) & ∀ a : carrier X, mem_upto a l }.

(** ** The subcategory of finite setoids *)

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinSets : Subcategory Sets :=
  @Build_Subcategory Sets FiniteSetoid
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition FinSetsCat : Category := Sub Sets FinSets.

Definition FinSets_Incl : FinSetsCat ⟶ Sets := Incl Sets FinSets.

(* Full as data, hence full as a functor. *)
Definition FinSets_Full : Subcategory.Full Sets FinSets :=
  fun _ _ _ _ _ => I.

Definition FinSets_Full_Functor : Functor.Full FinSets_Incl :=
  Full_Implies_Full_Functor Sets FinSets FinSets_Full.

(* Faithful by the generic argument of Construction/Subcategory.v, which is
   where the observation that it holds for every subcategory now lives. *)
Definition FinSets_Faithful : Functor.Faithful FinSets_Incl :=
  Incl_Faithful Sets FinSets.

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinSets_ShomRespects : ShomRespects Sets FinSets :=
  fun _ _ _ _ _ _ _ _ => I.

Definition FinSets_Full_roundtrip : Subcategory.Full Sets FinSets :=
  Full_Functor_Implies_Full Sets FinSets
    FinSets_ShomRespects FinSets_Full_Functor.

(** ** Two objects over the same setoid, and two distinct parallel arrows *)

(* The two-element setoid of Theory/Concrete.v is finite: `true` and `false`
   exhaust it. *)
Definition bool_finite : FiniteSetoid bool_setoid_object.
Proof.
  exists (cons true (cons false nil)).
  intro a; destruct a; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
Defined.

(* A second, deliberately redundant enumeration of the very same setoid. *)
Definition bool_finite_dup : FiniteSetoid bool_setoid_object.
Proof.
  exists (cons true (cons false (cons true nil))).
  intro a; destruct a; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
Defined.

Definition FinSets_bool : FinSetsCat := (bool_setoid_object; bool_finite).

Definition FinSets_bool_dup : FinSetsCat :=
  (bool_setoid_object; bool_finite_dup).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma FinSets_bool_same_image :
  FinSets_Incl FinSets_bool = FinSets_Incl FinSets_bool_dup.
Proof. reflexivity. Qed.

(* They are isomorphic in the subcategory, by the identity of [Sets] in both
   directions: the two enumerations differ, the underlying setoid does not. *)
Program Definition FinSets_bool_iso :
  FinSets_bool ≅[FinSetsCat] FinSets_bool_dup := {|
  to   := (id; I);
  from := (id; I)
|}.

(* Negation, as a morphism of the subcategory: the underlying [Sets]-morphism
   paired with the trivial [shom] witness. *)
Definition FinSets_negb : FinSets_bool ~{FinSetsCat}~> FinSets_bool :=
  (Sets_negb; I).

(* Non-vacuity.  [Sub]'s `≈` is `≈` of first projections, so distinctness of
   these two parallel morphisms of the subcategory reduces to distinctness of
   `id` and `negb` in [Sets] — Theory/Concrete.v's [Sets_two_arrows].  Stated
   with `→ False` because hom-equivalence here is `Type`-valued, so `¬`, which
   forces `Prop`, does not apply. *)
Lemma FinSets_two_arrows :
  @id FinSetsCat FinSets_bool ≈ FinSets_negb → False.
Proof.
  intro Heq.
  exact (Sets_two_arrows Heq).
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma FinSets_negb_Monic : Monic FinSets_negb.
Proof.
  apply (faithful_reflects_monic FinSets_Incl).
  apply (fst (injectivity_is_monic Sets_negb)).
  intros a b Hab; destruct a, b; simpl in *;
    solve [ reflexivity | discriminate ].
Qed.

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition enum_len (s : FinSetsCat) : nat := length (projT1 (projT2 s)).

(* So the two objects over the same setoid are genuinely different objects,
   even though the inclusion sends them to the same object of [Sets] and
   they are isomorphic in the subcategory. *)
Theorem FinSets_bool_distinct : FinSets_bool = FinSets_bool_dup → False.
Proof.
  intro Heq.
  assert (H : enum_len FinSets_bool = enum_len FinSets_bool_dup)
    by (rewrite Heq; reflexivity).
  simpl in H; discriminate.
Qed.
