Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * The free PROP 范畴 signature （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Free_category

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeCategory.

Context (S : Signature).

(** 本节：The hom-setoid: terms quotiented [TermEq]. （已译） *)
#[export] Program Instance Term_Setoid {m n : nat} : Setoid (Term S m n) := {|
  equiv := @TermEq S m n
|}.
Next Obligation.
  constructor.
  - intros t; apply TE_refl.
  - intros s t; apply TE_sym.
  - intros s t u; apply TE_trans.
Defined.

(** Composition is the [T_comp] constructor; it respects [TermEq] by
    [TE_comp_cong]. *)
#[export] Program Instance T_comp_respects {m n p : nat} :
  Proper (equiv ==> equiv ==> equiv) (@T_comp S m n p).
Next Obligation.
  proper.
  apply TE_comp_cong; assumption.
Qed.

(** Tensor (parallel composition) is also Proper for [TermEq], by
    [TE_tens_cong].  Allows [rewrite] under [T_tens]. *)
#[export] Program Instance T_tens_respects {m1 n1 m2 n2 : nat} :
  Proper (equiv ==> equiv ==> equiv) (@T_tens S m1 n1 m2 n2).
Next Obligation.
  proper.
  apply TE_tens_cong; assumption.
Qed.

(** The free category on [S]. *)
Program Definition FreeCat : Category := {|
  obj      := nat;
  hom      := @Term S;
  homset   := @Term_Setoid;
  id       := T_id;
  compose  := @T_comp S;
  compose_respects := @T_comp_respects;
  id_left  := fun m n f => TE_id_left f;
  id_right := fun m n f => TE_id_right f;
  comp_assoc := fun m n p q f g h => TE_sym _ _ (TE_assoc f g h);
  comp_assoc_sym := fun m n p q f g h => TE_assoc f g h
|}.

End FreeCategory.

Arguments FreeCat S : assert.
Arguments T_comp_respects {S m n p}.
