Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Ens_V, 范畴 sets belonging set V （已译） *)

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

(* 相关说明。 （已译） *)

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

(* The 含入 进入 ambient 范畴: decode 对象, 恒等
 态射, since [Spanned] 态射 already IS C-态射. （已译） *)
Program Definition Spanned_Incl : Spanned ⟶ C := {|
  fobj := El;
  fmap := λ _ _ f, f
|}.

(* It full — chosen preimage C-态射 态射 — is
 formal content "spanned El" being FULL subcategory. （已译） *)
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

(* * ** Ens_V over [Coq]: 对象 codes, arrows all functions （已译） *)

(* Mac Lane's Ens_V. The decoding lands bare types, so arrow an
 arbitrary function 态射 等价 pointwise Leibniz equality,
 exactly Instance/Coq.v. （已译） *)
Definition EnsV {V : Type} (El : V → Type) : Category := @Spanned Coq V El.

(* The 含入 Ens_V ⟶ Set, 全忠实 section above. （已译） *)
Definition EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  @Spanned_Incl Coq V El.

(* 相关说明。 （已译） *)
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

(* Identity 复合 "the usual" ones, Mac Lane's phrase. （已译） *)
Definition EnsV_id_is_identity {V : Type} (El : V → Type) (x : V) (a : El x) :
  @id (EnsV El) x a = a := eq_refl.

Definition EnsV_compose_is_usual {V : Type} (El : V → Type) (x y z : V)
           (f : @hom (EnsV El) y z) (g : @hom (EnsV El) x y) (a : El x) :
  (f ∘ g) a = f (g a) := eq_refl.

(* 相关说明。 （已译） *)

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

(* Arrows ALL setoid maps between decodings — again no side condition
 beyond respectfulness being 态射 [Sets] already means. （已译） *)
Definition EnsV_Sets_hom_is_all_setoid_maps {V : Type} (El : V → SetoidObject)
           (x y : V) :
  @hom (EnsV_Sets El) x y = SetoidMorphism (El x) (El y) := eq_refl.

Definition EnsV_Sets_equiv_is_pointwise {V : Type} (El : V → SetoidObject)
           (x y : V) (f g : @hom (EnsV_Sets El) x y) :
  (f ≈ g) = (∀ a : El x, f a ≈ g a) := eq_refl.

(* * ** The tautological family recovers ambient 范畴 （已译） *)

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

(* 相关说明。 （已译） *)
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

(* 相关说明。 （已译） *)
Definition EnsV_two_hom_up : @hom EnsV_two true false = (unit → bool) := eq_refl.

Definition EnsV_two_hom_down : @hom EnsV_two false true = (bool → unit) := eq_refl.
