Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * The free coloured-PROP 范畴 signature （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Free_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CFreeCategory.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** 本节：The hom-setoid: terms quotiented [CTermEq]. （已译） *)
#[export] Program Instance CTerm_Setoid {cs ds : list Colour} :
  Setoid (CTerm S cs ds) := {|
  equiv := @CTermEq Colour S cs ds
|}.
Next Obligation.
  constructor.
  - intros t; apply CTE_refl.
  - intros s t; apply CTE_sym.
  - intros s t u; apply CTE_trans.
Defined.

(** Composition is the [CT_comp] constructor; it respects [CTermEq] by
    [CTE_comp_cong]. *)
#[export] Program Instance CT_comp_respects {cs ds es : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@CT_comp Colour S cs ds es).
Next Obligation.
  proper.
  apply CTE_comp_cong; assumption.
Qed.

(** Tensor (parallel composition) is also Proper for [CTermEq], by
    [CTE_tens_cong].  Allows [rewrite] under [CT_tens]. *)
#[export] Program Instance CT_tens_respects
  {cs1 ds1 cs2 ds2 : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@CT_tens Colour S cs1 ds1 cs2 ds2).
Next Obligation.
  proper.
  apply CTE_tens_cong; assumption.
Qed.

(** The free category on [S]. *)
Program Definition CFreeCat : Category := {|
  obj      := list Colour;
  hom      := @CTerm Colour S;
  homset   := @CTerm_Setoid;
  id       := CT_id;
  compose  := @CT_comp Colour S;
  compose_respects := @CT_comp_respects;
  id_left  := fun cs ds f => CTE_id_left f;
  id_right := fun cs ds f => CTE_id_right f;
  comp_assoc := fun cs ds es fs f g h => CTE_sym _ _ (CTE_assoc f g h);
  comp_assoc_sym := fun cs ds es fs f g h => CTE_assoc f g h
|}.

End CFreeCategory.

Arguments CFreeCat {Colour} S : assert.
Arguments CT_comp_respects {Colour S cs ds es}.
Arguments CT_tens_respects {Colour S cs1 ds1 cs2 ds2}.

(* * * Parallel-复合 bifunctor CFreeCat （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CFreeTensor.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** The tensor bifunctor on [CFreeCat S]. *)
Program Definition CFreeCat_Tensor :
  CFreeCat S ∏ CFreeCat S ⟶ CFreeCat S := {|
  fobj := fun p => (fst p ++ snd p)%list;
  fmap := fun p q m =>
    @CT_tens Colour S (fst p) (fst q) (snd p) (snd q) (fst m) (snd m)
|}.
Next Obligation.
  unfold Proper, respectful.
  intros [f1 f2] [g1 g2] [Hf Hg]; simpl in *.
  apply CTE_tens_cong; assumption.
Qed.
Next Obligation.
  apply CTE_tens_id.
Qed.
Next Obligation.
  apply CTE_sym, CTE_interchange.
Qed.

End CFreeTensor.

Arguments CFreeCat_Tensor {Colour} S : assert.
