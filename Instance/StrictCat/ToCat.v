Require Import Category.Lib.
Require Import Equations.Prop.Logic.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** * The comparison functor [StrictCat ⟶ Cat] *)

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition iso_of_eq {C : Category} {x y : C} (p : x = y) : x ≅ y :=
  match p in (_ = z) return (x ≅ z) with
  | eq_refl => iso_id
  end.

(* Transporting a morphism along an equality of its codomain is the same as
   post-composing with the induced isomorphism. *)
Lemma transport_cod_to_iso {C : Category} {c a b : C} (p : a = b) (g : c ~> a) :
  transport (fun z => hom c z) p g ≈ to (iso_of_eq p) ∘ g.
Proof. destruct p; simpl; now rewrite id_left. Qed.

(* Dually, transporting along an equality of the domain (via [transport_r]) is
   pre-composition with the induced isomorphism. *)
Lemma transport_r_dom_to_iso {C : Category} {a b d : C} (p : a = b) (g : b ~> d) :
  transport_r (fun z => hom z d) p g ≈ g ∘ to (iso_of_eq p).
Proof. destruct p; unfold transport_r; simpl; now rewrite id_right. Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strict_equiv_implies_fun_equiv {C D : Category} (F G : C ⟶ D) :
  @equiv _ Functor_StrictEq_Setoid F G ->
  @equiv _ Functor_Setoid F G.
Proof.
  intros [eq_on_obj coh].
  exists (fun x => iso_of_eq (eq_on_obj x)).
  intros x y f.
  pose proof (coh x y f) as Hc.
  rewrite transport_cod_to_iso in Hc.
  rewrite transport_r_dom_to_iso in Hc.
  rewrite <- comp_assoc.
  rewrite <- Hc.
  rewrite comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

(* The comparison functor is the identity on both objects and morphisms; the
   only content is that it sends strict equality to natural isomorphism. *)
Program Definition StrictCat_to_Cat : StrictCat ⟶ Cat := {|
  fobj := fun C => C;
  fmap := fun _ _ F => F
|}.
Next Obligation.
  repeat intro.
  now apply strict_equiv_implies_fun_equiv.
Qed.
