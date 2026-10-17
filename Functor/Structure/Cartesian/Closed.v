Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Structure.Cartesian.

Generalizable All Variables.

(** Cartesian closed functors *)

(*
   nLab: https://ncatlab.org/nlab/show/closed+functor
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   本文件给出闭结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ClosedFunctor.

Context `{F : C ⟶ D}.
Context `{@CartesianFunctor C D F CA CB}.
Context `{@Closed C CA}.
Context `{@Closed D CB}.

Class ClosedFunctor := {
  fobj_exp_iso {x y : C} : F (y^x) ≅ F y ^ F x;   (* exponential comparison iso *)

  exp_in  := fun x y => from (@fobj_exp_iso x y);  (* F y ^ F x ~> F (y^x) *)
  exp_out := fun x y => to   (@fobj_exp_iso x y);  (* comparison: F (y^x) ~> F y ^ F x *)

  (* 相关说明。 （已译） *)
  fmap_curry {x y z : C} {f : x × y ~> z} :
    fmap (curry f) ≈ exp_in _ _ ∘ curry (fmap f ∘ prod_in);
  (* 相关说明。 （已译） *)
  fmap_uncurry {x y z : C} (f : x ~> z^y) :
    fmap (uncurry f) ≈ uncurry (exp_out _ _ ∘ fmap f) ∘ prod_out
}.

Context `{@ClosedFunctor}.

Arguments exp_in {_ _ _} /.
Arguments exp_out {_ _ _} /.

(* 相关说明。 （已译） *)
Corollary fmap_eval {x y : C} :
  fmap (@eval C _ _ x y) ≈ uncurry (curry eval ∘ exp_out) ∘ prod_out.
Proof.
  intros.
  unfold eval, eval'.
  rewrite fmap_uncurry; cat.
Qed.

Corollary exp_in_out {x y : C} :
  exp_in ∘ exp_out ≈ @id _ (F (y^x)).
Proof. apply iso_from_to. Qed.

#[local] Hint Rewrite @exp_in_out : functors.

Corollary exp_out_in {x y : C} :
  exp_out ∘ exp_in ≈ @id _ (F y ^ F x).
Proof. apply iso_to_from. Qed.

#[local] Hint Rewrite @exp_out_in : functors.

Corollary exp_in_inj {x y z : C} (f g : F x ~> F z ^ F y) :
  exp_in ∘ f ≈ exp_in ∘ g ↔ f ≈ g.
Proof.
  split; intros Hexp.
  - rewrite <- id_left.
    rewrite <- exp_out_in.
    rewrite <- comp_assoc.
    rewrite Hexp.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hexp.
    reflexivity.
Qed.

Corollary exp_out_inj {x y z : C} (f g : F x ~> F (z^y)) :
  exp_out ∘ f ≈ exp_out ∘ g ↔ f ≈ g.
Proof.
  split; intros Hexp.
  - rewrite <- id_left.
    rewrite <- exp_in_out.
    rewrite <- comp_assoc.
    rewrite Hexp.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hexp.
    reflexivity.
Qed.

End ClosedFunctor.

Arguments exp_in {_ _ _ _ _ _ _ _ _ _ _} /.
Arguments exp_out {_ _ _ _ _ _ _ _ _ _ _} /.

#[export] Hint Rewrite @exp_in_out : functors.
#[export] Hint Rewrite @exp_out_in : functors.
