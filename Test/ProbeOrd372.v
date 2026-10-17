(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件为测试：ProbeOrd372。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Ord.
Require Import Category.Instance.Ord.Poset.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** ** Instrument check *)

Fail Definition probe_ord372_instrument : nat := true.

(** ** Controls *)

Check @Poset_Reflective_in_Ord.
Check @Poset_reflector.
Check @Poset_adj.
Check @Pos_Sub.
Check @Pos_Sub_Full.
Check @Posets.
Check @Ord.
Check @OrdObject.
Check @OrdAntisymmetric.
Check @PosetReflection.
Check @PosetReflectionObj.
Check @reflection_proj.
Check @poset_unit.
Check @NatLe.
Check @NatLePos.
Check @Chaos2.
Check @MixOrd.
Check @Pos_to_Posets.
Check @Posets_to_Pos.
Check @Pos_Posets_strict_iso.
Check @posets_pos_posets_obj.
Check @OrdAsCategory.
Check @OrdHomAsFunctor.
Check @Subcategory.
Check @Reflective.
Check @Incl.
Check @Proset.
Check @PosetObject.

(** ** Negative 1 (CONVERSION) *)

Example ctrl_posets_round (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x
  := posets_pos_posets_obj x.

Fail Example neg_posets_round_strict (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x := eq_refl.

(** ** Negative 2 (CONVERSION) *)

Example ctrl_unit_pointwise (P : OrdObject)
    (x : carrier (ord_setoid P)) :
  ord_fn (poset_unit P) x = ord_fn (reflection_proj P) x := eq_refl.

Fail Example neg_unit_record (P : OrdObject) :
  poset_unit P = reflection_proj P := eq_refl.

(** ** Negative 3 (CONVERSION) *)

Example ctrl_natle_reflection_order :
  ord_le (PosetReflection NatLe) = ord_le NatLe := eq_refl.

Fail Example neg_natle_reflection_eq :
  PosetReflection NatLe = NatLe := eq_refl.

(** ** Negative 4 (TYPING) *)

Example ctrl_reflective_adj :
  Poset_reflector ⊣ Incl Ord Pos_Sub := Poset_adj.

Fail Example neg_adj_is_not_reflective :
  Reflective Pos_Sub := Poset_adj.

(*
   本节说明 ProbeOrd372 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example ctrl_ord_obj : obj[Ord] = OrdObject := eq_refl.

Example ctrl_thin_obj :
  obj[OrdAsCategory Chaos2] = carrier (ord_setoid Chaos2) := eq_refl.

Fail Example neg_ord_obj_is_not_points :
  obj[Ord] = obj[OrdAsCategory Chaos2] := eq_refl.

(** ** Negative 6 (FORMABILITY) *)

Section ProbeUniverses.
  Universes uo uh up.
  Constraint uh < up.
  Context (C : Category@{uo uh up}) (x y : C).

  Check (x ~> y).
  Check (@id C x).

  Fail Check (Subcategory C).
End ProbeUniverses.
