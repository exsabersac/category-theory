Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Ens_V, the category of sets belonging to a set V *)

(*
 nLab: https://ncatlab.org/nlab/show/category+of+sets
 nLab: https://ncatlab.org/nlab/show/full+subcategory
 nLab: https://ncatlab.org/nlab/show/type+universe

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/Grothendieck+universe
   Book: Mac Lane, CWM 2nd ed., §I.2, printed p. 11 (PDF p. 21)

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The full subcategory of C spanned by a family *)

(*
   nLab: https://ncatlab.org/nlab/show/full+subcategory

   本节说明 EnsV 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Spanned.

Context {C : Category}.
Context {V : Type}.
Context (El : V → C).

Definition Spanned : Category := {|
  obj     := V;                                    (* objects are the codes *)
  hom     := λ x y, El x ~> El y;                  (* ALL C-arrows between decodings *)
  homset  := λ x y, @homset C (El x) (El y);       (* C's hom-setoid, unchanged *)
  id      := λ x, @id C (El x);                    (* C's identity *)
  compose := λ x y z f g, @compose C (El x) (El y) (El z) f g;  (* C's composition *)

  compose_respects := λ x y z, @compose_respects C (El x) (El y) (El z);

  id_left  := λ x y, @id_left  C (El x) (El y);
  id_right := λ x y, @id_right C (El x) (El y);

  comp_assoc     := λ x y z w, @comp_assoc     C (El x) (El y) (El z) (El w);
  comp_assoc_sym := λ x y z w, @comp_assoc_sym C (El x) (El y) (El z) (El w)
|}.

(* The inclusion into the ambient category: decode on objects, and the identity
   on morphisms, since a [Spanned] morphism already IS a C-morphism. *)
Program Definition Spanned_Incl : Spanned ⟶ C := {|
  fobj := El;
  fmap := λ _ _ f, f
|}.

(* It is full — the chosen preimage of a C-morphism is that morphism — which is
   the formal content of "spanned by El" being a FULL subcategory. *)
#[export] Program Instance Spanned_Incl_Full : Full Spanned_Incl := {|
  prefmap := λ _ _ g, g
|}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Spanned_Incl_Faithful : Faithful Spanned_Incl := {|
  fmap_inj := λ _ _ _ _ H, H
|}.

End Spanned.

(** ** Ens_V over [Coq]: objects are codes, arrows are all functions *)

(* Mac Lane's Ens_V. The decoding lands in bare types, so an arrow is an
   arbitrary function and morphism equivalence is pointwise Leibniz equality,
   exactly as in Instance/Coq.v. *)
Definition EnsV {V : Type} (El : V → Type) : Category := @Spanned Coq V El.

(* The inclusion Ens_V ⟶ Set, full and faithful by the section above. *)
Definition EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  @Spanned_Incl Coq V El.

(* Statement fidelity, checked by conversion rather than argued.

   Objects are the members of V on the nose. *)
Definition EnsV_obj_is_V {V : Type} (El : V → Type) : @obj (EnsV El) = V := eq_refl.

(*
   本节说明 EnsV 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition EnsV_hom_is_all_functions {V : Type} (El : V → Type) (x y : V) :
  @hom (EnsV El) x y = (El x → El y) := eq_refl.

(* Two arrows are identified exactly when they agree pointwise. *)
Definition EnsV_equiv_is_pointwise {V : Type} (El : V → Type) (x y : V)
           (f g : @hom (EnsV El) x y) :
  (f ≈ g) = (∀ a : El x, f a = g a) := eq_refl.

(* Identity and composition are "the usual" ones, in Mac Lane's phrase. *)
Definition EnsV_id_is_identity {V : Type} (El : V → Type) (x : V) (a : El x) :
  @id (EnsV El) x a = a := eq_refl.

Definition EnsV_compose_is_usual {V : Type} (El : V → Type) (x y z : V)
           (f : @hom (EnsV El) y z) (g : @hom (EnsV El) x y) (a : El x) :
  (f ∘ g) a = f (g a) := eq_refl.

(** ** Ens_V over [Sets]: the setoid-flavoured variant *)

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition EnsV_Sets {V : Type} (El : V → SetoidObject) : Category :=
  @Spanned Sets V El.

Definition EnsV_Sets_Incl {V : Type} (El : V → SetoidObject) : EnsV_Sets El ⟶ Sets :=
  @Spanned_Incl Sets V El.

Definition EnsV_Sets_obj_is_V {V : Type} (El : V → SetoidObject) :
  @obj (EnsV_Sets El) = V := eq_refl.

(* Arrows are ALL setoid maps between the decodings — again no side condition
   beyond the respectfulness that being a morphism of [Sets] already means. *)
Definition EnsV_Sets_hom_is_all_setoid_maps {V : Type} (El : V → SetoidObject)
           (x y : V) :
  @hom (EnsV_Sets El) x y = SetoidMorphism (El x) (El y) := eq_refl.

Definition EnsV_Sets_equiv_is_pointwise {V : Type} (El : V → SetoidObject)
           (x y : V) (f g : @hom (EnsV_Sets El) x y) :
  (f ≈ g) = (∀ a : El x, f a ≈ g a) := eq_refl.

(** ** The tautological family recovers the ambient category *)

(*
   本节说明hom、等价、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 EnsV 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Spanned_recovers_ambient {C : Category} :
  @Spanned C (@obj C) (λ x, x) = C := eq_refl.

Definition EnsV_recovers_Coq : EnsV (λ T : Type, T) = Coq := eq_refl.

(* The same one universe over, for the setoid-flavoured variant and [Sets]. *)
Definition EnsV_Sets_recovers_Sets :
  EnsV_Sets (λ X : SetoidObject, X) = Sets := eq_refl.

(** ** A small Ens_V *)

(*
   本节说明 EnsV 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition EnsV_two_family (b : bool) : Type := if b then unit else bool.

Definition EnsV_two : Category := EnsV EnsV_two_family.

Definition EnsV_two_obj : @obj EnsV_two = bool := eq_refl.

(* The arrows from the one-element member to the two-element member are all
   functions unit → bool, and back again all functions bool → unit. *)
Definition EnsV_two_hom_up : @hom EnsV_two true false = (unit → bool) := eq_refl.

Definition EnsV_two_hom_down : @hom EnsV_two false true = (bool → unit) := eq_refl.
