Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(** * Cartesian (binary product) structure on [Sets] *)

(*
 nLab: https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   本文件给出笛卡尔结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Sets_Cartesian : @Cartesian Sets := {
  product_obj := fun x y =>
    {| carrier := (carrier x * carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
                       @equiv _ x (fst z) (fst w) *
                       @equiv _ y (snd z) (snd w)
          ; setoid_equiv := _
          |} |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation. proper; apply proper_morphism; assumption. Qed.
Next Obligation. all:firstorder. Qed.
