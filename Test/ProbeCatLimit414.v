(*
   本文件为测试：ProbeCatLimit414。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.

From Coq Require Import Eqdep_dec.

Require Import Category.Instance.Cat.Limit.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Check probe414_absent_name.

(* * ** N1-N3: index-below-对象 boundary [Cat] instance （已译） *)

Section IndexBoundary.

Universe i so sh.
Constraint so < sh.
Constraint i <= so.

(* Controls: product itself sits at small 范畴' own levels,
 对象 [Cat] over them, class formable up the
 projections. （已译） *)
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
         (PiCat C : Category@{so sh sh})).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
         (PiCat C : obj[Cat@{_ sh _ so sh}])).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
         @IsIndexedProduct Cat@{_ sh _ so sh} I C (PiCat C)).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) (a : I) =>
         PiCat_Proj C a).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh})
           (D : Category@{so sh sh}) (R : ∀ a, D ⟶ C a) => PiCat_ump R).

(* N1: donor. The projection's product cannot have 对象 universe
 [so] [so < sh]. （已译） *)
Fail Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) (a : I) =>
              (PiCat_Proj C a : PiCat@{i so sh so sh} C ⟶ C a)).

(* N2: inherited, firing at the argument [C]. *)
Fail Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
              PiCat_IsIndexedProduct C).

(* N3: inherited, the instance refused directly. *)
Fail Check @Cat_HasIndexedProducts@{i so sh _ _}.

End IndexBoundary.

(* 相关说明。 （已译） *)

Section StrictIndexBoundary.

Universe i h.
Constraint i < h.

(* Control: equalizers in [StrictCat] mention no index. *)
Check @StrictCat_HasEqualizers@{h _ _ _ _ _}.

(* 相关说明。 （已译） *)
Fail Check (fun (uip : ∀ C : Category@{h h h}, ObjUIP C)
                (fe : DepFunext@{h h}) =>
              (StrictCat_HasIndexedProducts uip fe
                 : HasIndexedProducts@{i i i _ _ h} StrictCat)).

(* Control: the completeness statement at its own shape. *)
Check (fun (uip : ∀ C : Category@{h h h}, ObjUIP C)
           (fe : DepFunext@{h h}) =>
         (StrictCat_Complete uip fe : Complete@{h h h _})).

(* N5: completeness over diagram shapes whose objects sit below [h]. *)
Fail Check (fun (uip : ∀ C : Category@{h h h}, ObjUIP C)
                (fe : DepFunext@{h h}) =>
              (StrictCat_Complete uip fe : Complete@{i h h _})).

(* N6: donor N5 — reduction 定理 itself demands index = hom. （已译） *)
Fail Check (fun (Cu : Category@{_ h h})
                (HP : HasIndexedProducts@{i i i _ _ h} Cu)
                (HE : HasEqualizers Cu) =>
              Complete_from_products_equalizers HP HE).

End StrictIndexBoundary.

(* 相关说明。 （已译） *)

Section StrictNotWeak.

Context {C D : Category} (F G : C ⟶ D) (uip : ObjUIP D).

Check (Eq_IsEqualizer F G uip
         : @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)).

Fail Check (Eq_IsEqualizer F G uip
              : @IsEqualizer Cat C D F G (EqCat F G) (EqIncl F G)).

End StrictNotWeak.

(* 相关说明。 （已译） *)

Section EqualizerTriangle.

Context {C D : Category} (F G : C ⟶ D) {Z : Category} (h : Z ⟶ C)
  (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Example eq_triangle_fobj :
  ∀ z, fobj[EqIncl F G ◯ Eq_med F G h Hh] z = fobj[h] z := fun _ => eq_refl.

Example eq_triangle_fmap :
  ∀ x y (f : x ~> y), fmap[EqIncl F G ◯ Eq_med F G h Hh] f = fmap[h] f
  := fun _ _ _ => eq_refl.

Fail Example eq_triangle_record :
  EqIncl F G ◯ Eq_med F G h Hh = h := eq_refl.

End EqualizerTriangle.

(* 相关说明。 （已译） *)

Section ProductTriangle.

Context {I : Type} (C : I → Category) {D : Category} (R : ∀ i, D ⟶ C i)
  (i : I).

Example pi_triangle_fobj :
  ∀ d, fobj[PiCat_Proj C i ◯ PiCat_Pair R] d = fobj[R i] d := fun _ => eq_refl.

Example pi_triangle_fmap :
  ∀ x y (f : x ~> y), fmap[PiCat_Proj C i ◯ PiCat_Pair R] f = fmap[R i] f
  := fun _ _ _ => eq_refl.

Fail Example pi_triangle_record :
  PiCat_Proj C i ◯ PiCat_Pair R = R i := eq_refl.

End ProductTriangle.

(** ** Positive readbacks *)

Section Readbacks.

Context {C D : Category} (F G : C ⟶ D) (uip : ∀ C : Category, ObjUIP C)
  {Z : Category} (h : Z ⟶ C)
  (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Example eq_mediator_is_Eq_med :
  unique_obj (eq_desc (Eq_IsEqualizer F G (uip D)) h Hh) = Eq_med F G h Hh
  := eq_refl.

Example strict_equalizer_obj :
  `1 (@equalizer StrictCat (StrictCat_HasEqualizers uip) C D F G) = EqCat F G
  := eq_refl.

Example strict_equalizer_map :
  `1 `2 (@equalizer StrictCat (StrictCat_HasEqualizers uip) C D F G)
  = EqIncl F G := eq_refl.

Example eqcat_is_sub : EqCat F G = Sub C (EqSub F G) := eq_refl.

Example eqincl_obj : ∀ x, fobj[EqIncl F G] x = `1 x := fun _ => eq_refl.

End Readbacks.

Section ProductReadbacks.

Context {A : Type} (C : A → Category).

Example cat_iprod_is_PiCat : @indexed_product Cat _ A C = PiCat C := eq_refl.

Example cat_iprod_proj_is_PiCat_Proj :
  ∀ a, @indexed_product_proj Cat _ A C a = PiCat_Proj C a := fun _ => eq_refl.

End ProductReadbacks.

(* 相关说明。 （已译） *)

Check EqCat_not_Cat_equalizer.
Check ChaoticBool_points_equiv.

(* * ** Guard block: every 常值 negative names, outside every [Fail] （已译） *)

Check @PiCat.
Check @PiCat_Proj.
Check @PiCat_Pair.
Check @PiCat_ump.
Check @PiCat_IsIndexedProduct.
Check @Cat_HasIndexedProducts.
Check @StrictCat_HasEqualizers.
Check @StrictCat_HasIndexedProducts.
Check @StrictCat_Complete.
Check @Complete_from_products_equalizers.
Check @DepFunext.
Check @ObjUIP.
Check @HasIndexedProducts.
Check @HasEqualizers.
Check @Complete.
Check @IsEqualizer.
Check @IsIndexedProduct.
Check @Eq_IsEqualizer.
Check @EqCat.
Check @EqIncl.
Check @EqSub.
Check @Eq_med.
Check @Cat.
Check @StrictCat.
