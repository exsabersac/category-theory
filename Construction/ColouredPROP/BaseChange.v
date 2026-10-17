Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example free_cstrict_braid {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  (cs ds : list Colour) :
  cstrict_braid (FreeColouredPROP S Cdec) cs ds = CT_braid cs ds := eq_refl.

Section BaseChange.

Context {Colour Colour' : Type}.
Context (f : Colour -> Colour').
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ColouredPROP_restrict (P : ColouredPROP Colour') :
  ColouredPROP Colour :=
  Build_ColouredPROP Colour
    (cprop_cat P)
    (cprop_strict P)
    (cprop_symmetric P)

    (* The coherence between two [Monoidal] paths [P]'s own
 证明: both paths project through untouched structures. （已译） *)
    (@cprop_monoidal_coherence Colour' P)

    (* Objects: colour words over [Colour], read through [map f]. *)
    (fun cs : list Colour => @cprop_of_list Colour' P (map f cs))

    (* 相关说明。 （已译） *)
    (@cprop_unit_nil Colour' P)

    (* The tensor condition: [P]'s own strictness at image words,
 composed [cprop_of_list]-image (propositional)
 幺半群-homomorphism law [map f]. （已译） *)
    (fun cs ds : list Colour =>
       eq_trans (@cprop_tensor_app Colour' P (map f cs) (map f ds))
                (f_equal (@cprop_of_list Colour' P)
                         (eq_sym (map_app f cs ds)))).

(** Machine-checked: restriction changes 对象 naming. （已译） *)

Example ColouredPROP_restrict_cat (P : ColouredPROP Colour') :
  cprop_cat (ColouredPROP_restrict P) = cprop_cat P := eq_refl.

Example ColouredPROP_restrict_of_list (P : ColouredPROP Colour')
  (cs : list Colour) :
  cprop_of_list (ColouredPROP := ColouredPROP_restrict P) cs
  = cprop_of_list (ColouredPROP := P) (map f cs) := eq_refl.

Example ColouredPROP_restrict_unit (P : ColouredPROP Colour') :
  @cprop_unit_nil Colour (ColouredPROP_restrict P)
  = @cprop_unit_nil Colour' P := eq_refl.

(** 本节：A restricted wire wire image colour ([map f [c]]
 computes [[f c]]). （已译） *)
Example ColouredPROP_restrict_wire (P : ColouredPROP Colour') (c : Colour) :
  wire (P := ColouredPROP_restrict P) c = wire (P := P) (f c) := eq_refl.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CSigMap (S : CSignature Colour) (S' : CSignature Colour') : Type :=
  forall cs ds : list Colour, S cs ds -> S' (map f cs) (map f ds).

Context (S : CSignature Colour).
Context (S' : CSignature Colour').
Context (h : CSigMap S S').

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition basechange_target : ColouredPROP Colour :=
  ColouredPROP_restrict (FreeColouredPROP S' C'dec).

Definition basechange_val : CValuation basechange_target S :=
  fun (cs ds : list Colour) (g : S cs ds) => CT_gen (h cs ds g).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition BaseChangeF : CFreeCat S ⟶ CFreeCat S' :=
  @CInterpF Colour S basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(*
   本节说明 BaseChange 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example BaseChangeF_fobj (cs : list Colour) :
  fobj[BaseChangeF] cs = map f cs := eq_refl.

Example BaseChangeF_gen {cs ds : list Colour} (g : S cs ds) :
  fmap[BaseChangeF] (CT_gen g) = CT_gen (h cs ds g) := eq_refl.

(*
   本节说明 BaseChange 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example BaseChangeF_fmap_id (cs : list Colour) :
  fmap[BaseChangeF] (CT_id cs) = CT_id (map f cs) := eq_refl.

Example BaseChangeF_fmap_comp {cs ds es : list Colour}
  (u : CTerm S ds es) (t : CTerm S cs ds) :
  fmap[BaseChangeF] (CT_comp u t)
  = CT_comp (fmap[BaseChangeF] u) (fmap[BaseChangeF] t) := eq_refl.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition BaseChangeF_Monoidal :
  @MonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec) BaseChangeF :=
  @CInterpF_Monoidal Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

Definition BaseChangeF_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec) BaseChangeF :=
  @CInterpF_Strict Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(** Machine-checked: the unit comparison is reflexivity... *)
Example BaseChangeF_strict_pure_obj_is_refl :
  @strict_pure_obj _ _ _ _ BaseChangeF BaseChangeF_Strict = eq_refl
  := eq_refl.

(*
   本节说明 BaseChange 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example BaseChangeF_strict_ap_obj_is_tensor_app (cs ds : list Colour) :
  @strict_ap_obj _ _ _ _ BaseChangeF BaseChangeF_Strict cs ds
  = @cprop_tensor_app Colour basechange_target cs ds := eq_refl.

Example basechange_tensor_app_shape (cs ds : list Colour) :
  @cprop_tensor_app Colour basechange_target cs ds
  = eq_trans eq_refl
      (f_equal (fun ks : list Colour' => ks) (eq_sym (map_app f cs ds)))
  := eq_refl.

Definition BaseChangeF_Braided :
  @BraidedMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided S' C'dec) BaseChangeF :=
  @CInterpF_Braided Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example BaseChangeF_Braided_is_strong :
  @braided_is_strong _ _ _ _ BaseChangeF BaseChangeF_Braided
  = BaseChangeF_Monoidal := eq_refl.

(** A braided monoidal functor between symmetric monoidal categories
    IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition BaseChangeF_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Symmetric S Cdec) (CFreeCat_Symmetric S' C'dec) BaseChangeF :=
  BaseChangeF_Braided.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition BaseChangeF_SymmetricStrict :
  CSymmetricStrict S Cdec basechange_target BaseChangeF BaseChangeF_Monoidal :=
  @CInterpF_SymmetricStrict Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(*
   本节说明 BaseChange 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example basechange_cstrict_braid (xs ys : list Colour') :
  cstrict_braid basechange_target xs ys = CT_braid xs ys := eq_refl.

End BaseChange.

Arguments ColouredPROP_restrict {Colour Colour'} f P : assert.
Arguments CSigMap {Colour Colour'} f S S' : assert.
Arguments basechange_target {Colour Colour'} f C'dec S' : assert.
(*
   本节说明 BaseChange 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Arguments BaseChangeF {Colour Colour'} f C'dec S S' h : assert.
Arguments BaseChangeF_Monoidal {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Strict {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Braided {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Symmetric {Colour Colour'} f Cdec C'dec S S' h : assert.
(* [BaseChangeF_SymmetricStrict] keeps its auto-generated argument
 status: its type [CSymmetricStrict ...] is definitionally
 unfolding ∀, so constant carries 边界 binders [cs ds]
 as trailing arguments (compare [CInterpF_SymmetricStrict] in
 [Construction/ColouredPROP/Universal.v]).（已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
