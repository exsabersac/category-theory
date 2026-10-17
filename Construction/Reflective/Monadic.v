(*
    nLab: https://ncatlab.org/nlab/show/reflective+subcategory
    nLab: https://ncatlab.org/nlab/show/monadic+functor
    nLab: https://ncatlab.org/nlab/show/idempotent+monad

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.

Generalizable All Variables.

(* * ** The comparison 函子 reflection （已译） *)

(*
   本节说明伴随、单子、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition reflective_comparison@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Sub C S ⟶ @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)
  := EM_Comparison (reflective_adj R).

Definition reflective_comparison_Faithful@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Faithful (reflective_comparison R).
Proof. constructor; intros x y f g H; exact H. Defined.

(* A 态射 algebras between two comparison algebras arrow of
 C between 对象 subcategory; fullness subcategory puts
 it back [Sub C S]. （已译） *)
Definition reflective_comparison_prefmap@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) {s t : Sub C S}
  (h : reflective_comparison R s ~> reflective_comparison R t) : s ~> t :=
  (t_alg_hom[h]; reflective_full R _ _ `2 s `2 t t_alg_hom[h]).

Definition reflective_comparison_Full@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Functor.Full (reflective_comparison R).
Proof.
  refine {| prefmap := @reflective_comparison_prefmap C S R |}.
  intros s t h; simpl; reflexivity.
Defined.

(* 相关说明。 （已译） *)
Definition reflective_eso_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  Sub C S := reflector R ``z.

(*
   本节说明 Monadic 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition reflective_eso_iso@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  reflective_comparison R (reflective_eso_obj R z) ≅ z.
Proof.
  destruct z as [a alg].
  pose (Hret := @algebra_ret_iso C _ (Reflective_Monad R)
                  (Reflective_IdempotentMonad R) a alg).
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R))
       (reflective_comparison R (reflective_eso_obj R (a; alg))) (a; alg)
       _ _ _ _).
  - refine (@Build_TAlgebraHom C _ (Reflective_Monad R) _ _ _ _
              (t_alg[alg]) _).
    simpl. symmetry. exact (@t_action C _ (Reflective_Monad R) a alg).
  - refine (@Build_TAlgebraHom C _ (Reflective_Monad R) _ _ _ _
              (@ret C _ (Reflective_Monad R) a) _).
    simpl.
    transitivity (@id C (fobj[Incl C S ◯ reflector R] a)).
    + exact (@is_right_inverse C _ _ _ Hret).
    + symmetry. exact (@join_fmap_ret C _ (Reflective_Monad R) a).
  - simpl. exact (@t_id C _ (Reflective_Monad R) a alg).
  - simpl. exact (@is_right_inverse C _ _ _ Hret).
Defined.

Definition reflective_comparison_ESO@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  EssentiallySurjective (reflective_comparison R) :=
  @Build_EssentiallySurjective _ _ (reflective_comparison R)
    (reflective_eso_obj R) (reflective_eso_iso R).

(** ** Riehl, Proposition 5.3.3 (ii) *)

(* The subcategory ITSELF equivalent algebras induced
 idempotent 单子, comparison 函子. （已译） *)
Definition Reflective_EM_Equivalence@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  EquivalenceOfCategories (reflective_comparison R) :=
  @FF_ESO_Equivalence _ _ (reflective_comparison R)
    (reflective_comparison_Full R) (reflective_comparison_Faithful R)
    (reflective_comparison_ESO R).

(* The 含入 reflective subcategory monadic, in
 Monad/Comparison.v's sense: reflector, reflection, the
 等价 above. （已译） *)
Definition Reflective_Monadic@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) : Monadic (Incl C S) :=
  (reflector R; (reflective_adj R; Reflective_EM_Equivalence R)).

(** ** Readbacks *)

(* The comparison sends 对象 subcategory own carrier,
 counit read through 含入 structure map. （已译） *)
Example reflective_comparison_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (s : Sub C S) :
  ``(reflective_comparison R s) = `1 s := eq_refl.

Example reflective_comparison_alg@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (s : Sub C S) :
  t_alg[projT2 (reflective_comparison R s)]
    = fmap[Incl C S] (@counit _ _ _ _ (reflective_adj R) s) := eq_refl.

(* 相关说明。 （已译） *)
Example reflective_eso_obj_is_reflector@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  reflective_eso_obj R z = fobj[reflector R] ``z := eq_refl.

(* The 同构's forward leg IS algebra's structure map. （已译） *)
Example reflective_eso_iso_to@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (a : C)
  (alg : @TAlgebra C _ (Reflective_Monad R) a) :
  t_alg_hom[to (reflective_eso_iso R (a; alg))] = t_alg[alg] := eq_refl.

(* The monadic witness's 左伴随 reflector itself. （已译） *)
Example Reflective_Monadic_left@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  `1 (Reflective_Monadic R) = reflector R := eq_refl.
