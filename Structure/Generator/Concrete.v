Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(*
   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/well-pointed+category

   本文件给出具体范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Bridge.

Context {C : Category}.

(** ** The two spellings of Awodey's condition *)

(* [Separator] (Theory/Concrete.v) is the class form, whose field
   [separates] takes its two objects implicitly; [IsSeparator]
   (Structure/Generator.v) is the Type-valued form that the
   characterizations consume as a function.  Nothing moves but the
   packaging. *)
Definition Separator_of_IsSeparator (c : C) (H : IsSeparator c) :
  Separator c := @Build_Separator C c (fun x y f g E => H x y f g E).

Definition IsSeparator_of_Separator (c : C) (S : Separator c) :
  IsSeparator c := fun x y f g E => @separates C c S x y f g E.

(* The forward half of Awodey's characterization is already in the tree,
   though only as the [underlying_faithful] obligation of
   Theory/Concrete.v's concretization.  Recovering it that way gives
   the same statement as Structure/Generator.v's [separator_faithful],
   and this is the check that the two developments agree. *)
Example separator_faithful_via_concrete (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @underlying_faithful C
    (@Concrete_of_Separator C c (Separator_of_IsSeparator c H)).

End Bridge.
