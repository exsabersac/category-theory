(*
   本文件为测试：ProbeFunEval424。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Exponential.
Require Import Category.Instance.Fun.Eval.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Theory.Shapes.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Representable.Functorial.
Require Import Category.Adjunction.Diagonal.Connected.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Theory.Lawvere.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe424_absent_name.

(* 相关说明。 （已译） *)

Section EvalAtAgreement.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}} (p : P).

(* controls: the two data fields convert *)
Example p424_EvalAt_obj : fobj[Eval p] = fobj[@EvalAt P X p] := eq_refl.

Example p424_EvalAt_map (H K : [P, X]) :
  @fmap _ _ (Eval p) H K = @fmap _ _ (@EvalAt P X p) H K := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p424_EvalAt_record : Eval p = @EvalAt P X p := eq_refl.

End EvalAtAgreement.

(* 相关说明。 （已译） *)

Section PartialAgreement.

Context {P X : Category} (p : P) (H K : [P, X]).

(* control: on objects, on the nose *)
Example p424_partial_obj : fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(* N2 CONVERSION: arrows partial's action [bimap s id], carrying
 [fmap id] 函子 law removes （已译） *)
Fail Example p424_partial_map (s : H ~{[P, X]}~> K) :
  @fmap _ _ (Eval p) H K s = @fmap _ _ (Partial_l EvalBi p) H K s := eq_refl.

(* control: it closes at ≈, and is packaged as an isomorphism *)
Check (eval_partial_map p H K).
Check (eval_partial_iso p).

(* 相关说明。 （已译） *)
Fail Example p424_partial_r_map (q : P) (f : p ~> q) :
  @fmap _ _ (Partial_r EvalBi H) p q f = @fmap _ _ H p q f := eq_refl.

(* controls: on objects on the nose, on arrows at ≈ *)
Example p424_partial_r_obj : fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.
Check (fun (q : P) (f : p ~> q) => eval_partial_r_map H p q f).

End PartialAgreement.

(* * ** C: same data tree's other evaluation 函子 （已译） *)

(* at [X := Sets]: Functor/Hom/Yoneda/Natural.v's [YoEvalAt] *)
Example p424_YoEvalAt_obj {C : Category} (c : C) :
  fobj[@Eval C Sets c] = fobj[@YoEvalAt C c] := eq_refl.

Example p424_YoEvalAt_map {C : Category} (c : C) (F G : [C, Sets]) :
  @fmap _ _ (@Eval C Sets c) F G = @fmap _ _ (@YoEvalAt C c) F G := eq_refl.

(* at [P := _1]: Theory/Shapes.v's [One_Eval], both fields *)
Example p424_One_Eval_obj {X : Category} :
  fobj[@Eval _1 X ttt] = fobj[@One_Eval X] := eq_refl.

Example p424_One_Eval_map {X : Category} (F G : [_1, X]) :
  @fmap _ _ (@Eval _1 X ttt) F G = @fmap _ _ (@One_Eval X) F G := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Notation BNat := (Deloop Nat_Plus).

Example p424_prior_nat (n : nat) (F : [BNat, Sets]) :
  transform[wit_ev_tau n] F = transform[@Eval_nat BNat Sets ttt ttt n] F
  := eq_refl.

(* [Cat_Closed]'s own evaluation, named in Instance/Fun/Eval/Cat.v *)
Check (@CatEval_map).
Check (@eval_transpose).

(* 相关说明。 （已译） *)

Section Ev1.

Context (T : LawvereTheory).

(* [Models T Sets] full subcategory [[law_cat T, Sets]] cut out
 [Models_sub]; [ev1] evaluation at generator after the
 含入. （已译） *)
Definition p424_ev1_via_Eval : Models T Sets ⟶ Sets :=
  @Eval (@law_cat T) Sets (law_of_nat 1%nat)
    ◯ @Incl (@Fun (@law_cat T) Sets) (Models_sub T Sets).

Example p424_ev1_obj (M : Models T Sets) :
  fobj[ev1 T] M = fobj[p424_ev1_via_Eval] M := eq_refl.

Example p424_ev1_map (M N : Models T Sets) :
  @fmap _ _ (ev1 T) M N = @fmap _ _ p424_ev1_via_Eval M N := eq_refl.

End Ev1.

(** ** E: readbacks *)

Check (@EvalFunctor_obj).
Check (@EvalFunctor_map).
Check (@eval_partial_r_obj).
Check (@eval_partial_r_map).

(** ** Guard block *)

Check @Eval.
Check @EvalBi.
Check @Eval_nat.
Check @EvalFunctor.
Check @eval_partial_obj.
Check @eval_partial_map.
Check @eval_partial_iso.
Check @CatEval.
Check @CatEval_obj.
Check @eval_is_CatEval_partial_obj.
Check @eval_is_CatEval_partial_map.
Check @EvalAt.
Check @Partial_l.
Check @Partial_r.
Check @bimap.
Check @fmap.
Check @fobj.
