Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * Preadditive categories *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Preadditive_category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Preadditive (C : Category) := {
  padd {x y : C} : (x ~> y) -> (x ~> y) -> (x ~> y);
  pzero {x y : C} : x ~> y;

  padd_respects {x y : C} :
    Proper (equiv ==> equiv ==> equiv) (@padd x y);

  (* (hom(x,y), padd, pzero) is a commutative monoid. *)
  padd_assoc {x y : C} (f g h : x ~> y) :
    padd (padd f g) h ≈ padd f (padd g h);
  padd_comm {x y : C} (f g : x ~> y) :
    padd f g ≈ padd g f;
  padd_zero_left {x y : C} (f : x ~> y) :
    padd pzero f ≈ f;

  (* Composition is additive in each argument separately. *)
  compose_padd_left {x y z : C} (h : y ~> z) (f g : x ~> y) :
    h ∘ padd f g ≈ padd (h ∘ f) (h ∘ g);
  compose_padd_right {x y z : C} (f g : y ~> z) (h : x ~> y) :
    padd f g ∘ h ≈ padd (f ∘ h) (g ∘ h);

  (* The additive unit absorbs composition on both sides. *)
  compose_pzero_left {x y z : C} (f : x ~> y) :
    @pzero y z ∘ f ≈ pzero;
  compose_pzero_right {x y z : C} (f : y ~> z) :
    f ∘ @pzero x y ≈ pzero
}.

#[export] Existing Instance padd_respects.

(* 相关说明。 （已译） *)
Corollary padd_zero_right {C : Category} `{P : @Preadditive C} {x y : C}
  (f : x ~> y) :
  padd f pzero ≈ f.
Proof.
  rewrite padd_comm.
  apply padd_zero_left.
Qed.

(* 相关说明。 （已译） *)
Declare Scope addition_scope.
Delimit Scope addition_scope with padd.

Infix "+" := padd : addition_scope.
Notation "0" := pzero : addition_scope.

(*
   本节说明 Preadditive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pzero_zero_mor {C : Category} `{P : @Preadditive C} `{Z : @ZeroObject C}
  {x y : C} :
  @pzero C P x y ≈ @zero_mor C Z x y.
Proof.
  rewrite <- (@zero_mor_unique C Z x y
                (@one C (@zero_terminal C Z) x)
                (@pzero C P (@initial_obj C (@zero_initial C Z)) y)).
  (* Goal: pzero ≈ (pzero ∘ zero_coincide) ∘ one. Each 复合 with
 [pzero] left collapses [compose_pzero_left]. （已译） *)
  rewrite compose_pzero_left.
  rewrite compose_pzero_left.
  reflexivity.
Qed.
