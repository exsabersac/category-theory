Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(** The comma 范畴 over terminal 范畴 product 范畴. （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProductComma.

(* Build 同构 (and 函子, naturals, proofs) repeatedly
 peeling head connective goal discharging leaf the
 appropriate 范畴 tactic. （已译） *)
Ltac simpl_cat :=
  repeat (
    simpl; intros;
    simplify;
    simpl; intros;
    match goal with
    | [ |- _ ≅ _ ] => unshelve econstructor
    | [ |- _ ⟹ _ ] => unshelve econstructor
    | [ |- _ ⟶ _ ] => unshelve econstructor
    | [ |- @Proper _ _ _ ] => first [ abstract proper | proper ]
    | [ |- @Equivalence _ _ ] => first [ abstract equivalence | equivalence ]
    | [ |- _ ≈ _ ] => abstract cat
    | _ => cat
    end).

Theorem Comma_Product {C : Category} {D : Category}
        (F : C ⟶ 1) (G : D ⟶ 1) :
  (F ↓ G) ≅[Cat] C ∏ D.
Proof. simpl_cat. Qed.

End ProductComma.
