Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProductClosed.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.
Context `{@Closed C _}.
Context `{@Closed D _}.

Program Instance Product_Closed : @Closed (C ∏ D) Product_Cartesian := {
  (* internal hom, componentwise: (e,f) ^ (c,d) = (e^c, f^d) *)
  exponent_obj := fun x y => (fst y ^ fst x, snd y ^ snd x);
  (* currying iso, the factorwise pairing of the component exp_iso's *)
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    (to exp_iso (fst f), to exp_iso (snd f)) |}
     ; from := {| morphism := fun f =>
                    (from exp_iso (fst f), from exp_iso (snd f)) |} |}
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. split; exact (iso_to_from (@exp_iso _ _ _ _ _ _) _). Qed.
Next Obligation. split; exact (iso_from_to (@exp_iso _ _ _ _ _ _) _). Qed.

End ProductClosed.
