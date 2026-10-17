(** * Models are closed under product-preserving functors *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   nLab:      https://ncatlab.org/nlab/show/product-preserving+functor
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   本文件给出模型闭包相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.

Generalizable All Variables.

Section FunctorClosure.

Context {B C D : Category}.
Context `{CB : @Cartesian B}.
Context `{TB : @Terminal B}.
Context `{CC : @Cartesian C}.
Context `{TC : @Terminal C}.
Context `{CD : @Cartesian D}.
Context `{TD : @Terminal D}.

Context (F : B ⟶ C) (K : C ⟶ D).
Context (FC : @CartesianFunctor B C F CB CC).
Context (KC : @CartesianFunctor C D K CC CD).

Program Definition CartesianFunctor_Compose :
  @CartesianFunctor B D (K ◯ F) CB CD := {|
  fobj_prod_iso := fun x y =>
    iso_compose (@fobj_prod_iso C D K CC CD KC (F x) (F y))
                (fobj_iso K _ _ (@fobj_prod_iso B C F CB CC FC x y))
|}.
Next Obligation.
  rewrite (@fmap_exl B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_exl C D K CC CD KC).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite (@fmap_exr B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_exr C D K CC CD KC).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite (@fmap_fork B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_fork C D K CC CD KC).
  now rewrite comp_assoc.
Qed.

Context (FT : @TerminalFunctor B C F TB TC).
Context (KT : @TerminalFunctor C D K TC TD).

Program Definition TerminalFunctor_Compose :
  @TerminalFunctor B D (K ◯ F) TB TD := {|
  fobj_one_iso :=
    iso_compose (fobj_iso K _ _ (@fobj_one_iso B C F TB TC FT))
                (@fobj_one_iso C D K TC TD KT)
|}.
Next Obligation.
  rewrite (@fmap_one B C F TB TC FT).
  rewrite fmap_comp.
  rewrite (@fmap_one C D K TC TD KT).
  now rewrite comp_assoc.
Qed.

End FunctorClosure.

Section ModelClosure.

Context (T : LawvereTheory).
Context {C D : Category}.
Context `{CC : @Cartesian C}.
Context `{TC : @Terminal C}.
Context `{CD : @Cartesian D}.
Context `{TD : @Terminal D}.
Context (K : C ⟶ D).
Context (KC : @CartesianFunctor C D K CC CD).
Context (KT : @TerminalFunctor C D K TC TD).

Definition Model_Compose (M : @Model T C CC TC) : @Model T D CD TD :=
  {| model_fun := K ◯ @model_fun T C CC TC M
   ; model_cartesian :=
       @CartesianFunctor_Compose (@law_cat T) C D (@law_cartesian T) CC CD
         (@model_fun T C CC TC M) K (@model_cartesian T C CC TC M) KC
   ; model_terminal :=
       @TerminalFunctor_Compose (@law_cat T) C D (@law_terminal T) TC TD
         (@model_fun T C CC TC M) K (@model_terminal T C CC TC M) KT |}.

Example Model_Compose_fun (M : @Model T C CC TC) :
  @model_fun T D CD TD (Model_Compose M) = K ◯ @model_fun T C CC TC M
  := eq_refl.

Definition Models_Compose_obj (x : @Models T C CC TC) : @Models T D CD TD :=
  @Model_pack T D CD TD (Model_Compose (@Model_unpack T C CC TC x)).

End ModelClosure.

